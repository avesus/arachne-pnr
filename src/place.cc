/* Copyright (C) 2015 Cotton Seed
   
   This file is part of arachne-pnr.  Arachne-pnr is free software;
   you can redistribute it and/or modify it under the terms of the GNU
   General Public License version 2 as published by the Free Software
   Foundation.
   
   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program. If not, see <http://www.gnu.org/licenses/>. */

#include "util.hh"
#include "casting.hh"
#include "place.hh"
#include "netlist.hh"
#include "chipdb.hh"
#include "location.hh"
#include "configuration.hh"
#include "pcf.hh"
#include "carry.hh"
#include "bitvector.hh"
#include "ullmanset.hh"
#include "hashmap.hh"
#include "designstate.hh"
#include "global.hh"

#include <iomanip>
#include <vector>
#include <set>
#include <random>
#include <algorithm>
#include <iostream>
#include <cassert>
#include <cmath>
#include <ctime>

class Placer
{
public:
  random_generator &rg;
  
  DesignState &ds;
  const ChipDB *chipdb;
  const Package &package;
  Design *d;
  Models &models;
  Model *top;
  const CarryChains &chains;
  const Constraints &constraints;
  const std::map<Instance *, uint8_t, IdLess> &gb_inst_gc;
  std::map<Instance *, int, IdLess> &placement;
  Configuration &conf;
  
  std::vector<int> logic_columns;
  std::vector<int> logic_tiles,
    ramt_tiles;
  
  std::vector<std::vector<int>> related_tiles;
  
  std::vector<Net *> nets;
  std::map<Net *, int, IdLess> net_idx;
  
  int n_gates;
  BasedVector<Instance *, 1> gates;
  std::map<Instance *, int, IdLess> gate_idx;
  
  std::map<int, std::vector<int>> global_cells;
  
  std::vector<std::vector<int>> cell_type_empty_cells;

  BasedBitVector<1> locked;
  BasedBitVector<1> chained;
  
  BasedVector<int, 1> gate_clk, gate_sr, gate_cen, gate_latch;
  
  BasedVector<std::vector<int>, 1> gate_local_np;
  UllmanSet tmp_local_np;
  
  BitVector net_global;
  
  std::vector<int> free_gates;
  
  BasedVector<int, 1> gate_chain;
  
  CellType gate_cell_type(int g);

  int gate_random_cell(int g);
  std::pair<Location, bool> chain_random_loc(unsigned c);
  
  void move_gate(int g, int cell);
  void move_chain(unsigned c, const Location &new_loc);
  
  int tile_n_pos(int t);
  
  std::vector<std::vector<int>> net_gates;
  BasedVector<std::vector<int>, 1> gate_nets;
  
  int diameter;
  double temp;
  bool improved;
  int n_move;
  int n_accept;
  
  bool move_failed;
  UllmanSet changed_tiles;
  std::vector<std::pair<int, int>> restore_cell;
  std::vector<std::tuple<int, int, int>> restore_chain;
  std::vector<std::pair<int, int>> restore_net_length;
  UllmanSet recompute;
  
  void save_set(int cell, int g);
  
  void save_set_chain(int c, int x, int y);
  int save_recompute_wire_length();
  void restore();
  void discard();
  void accept_or_restore();
  
  std::vector<int> chain_x, chain_y;
  
  BasedVector<int, 1> gate_cell;
  BasedVector<int, 1> cell_gate;
  
  std::vector<int> net_length;
  
  bool inst_drives_global(Instance *inst, int c, int glb);
  bool valid_global(int glb);
  bool valid(int t);
  
  int wire_length() const;
  int compute_net_length(int w);
  unsigned top_port_io_gate(const std::string &net_name);

  bool free_tile(int x, int y);
  bool free_tiles(int x, int y, int nt);
  int find_free_tiles(int x, int nt);

  int alloc_cell(CellType celltype, int gate);
  int alloc_tiles(int nt);

  void place_gate(int gate, int cell, bool chain, bool lock);

  void place_chain(const std::vector<Instance*> &chain, int t, bool lock);

  void place_initial();

  void configure_io(const Location &loc,
                    bool enable_input,
                    bool pullup);
  void configure();
  
#ifndef NDEBUG
  void check();
#endif
  
public:
  Placer(random_generator &rg_, DesignState &ds_);
  
  void place();
};

CellType
Placer::gate_cell_type(int g)
{
  Instance *inst = gates[g];
  if (models.is_lc(inst))
    return CellType::LOGIC;
  else if (models.is_ioX(inst))
    return CellType::IO;
  else if (models.is_gb(inst))
    return CellType::GB;
  else if (models.is_warmboot(inst))
    return CellType::WARMBOOT;
  else if (models.is_pllX(inst))
    return CellType::PLL;
  else
    {
      assert(models.is_ramX(inst));
      return CellType::RAM;
    }
}

int
Placer::gate_random_cell(int g)
{
  CellType ct = gate_cell_type(g);
  if (ct == CellType::LOGIC)
    {
      int cell = gate_cell[g];
      int t = chipdb->cell_location[cell].tile();
      int x = chipdb->tile_x(t),
          y = chipdb->tile_y(t);
      
    L:
      int new_x = rg.random_int(std::max(0, x - diameter),
                                std::min(chipdb->width-1, x + diameter)),
          new_y = rg.random_int(std::max(0, y - diameter),
                                std::min(chipdb->height-1, y + diameter));
      int new_t = chipdb->tile(new_x, new_y);
      if (chipdb->tile_type[new_t] != TileType::LOGIC)
        goto L;
      
      Location loc(new_t, rg.random_int(0, 7));
      return  chipdb->loc_cell(loc);
    }
  else
    {
      int ct_idx = cell_type_idx(ct);
      return random_element(chipdb->cell_type_cells[ct_idx], rg);
    }
}

std::pair<Location, bool>
Placer::chain_random_loc(unsigned c)
{
  int nt = (chains.chains[c].size() + 7) / 8;
  
  int new_x = random_element(logic_columns, rg);
  int new_y = random_int(1, chipdb->height - 2 - (nt - 1), rg);
  int new_y_end = new_y + nt;

  // check that the new loc doesn't overlap any chains
  for (unsigned e = 0; e < chains.chains.size(); ++e)
    {
      if (chain_x[e] != new_x)  // including self
        continue;
      
      int e_nt = (chains.chains[e].size() + 7) / 8;
      int e_y = chain_y[e];
      int e_y_end = e_y + e_nt;

      // if the new position overlaps a chain, return false?
      //   not exactly sure of the logic here ...
      if ((new_y     > e_y && new_y     < e_y_end)
       || (new_y_end > e_y && new_y_end < e_y_end))
        return std::make_pair(Location(), false);
    }
  
  // check that the new loc doesn't overlap any locked gates
  for( int y = new_y; y < new_y_end; y++ ) {
      int t = chipdb->tile(new_x, y);
      for( int z = 0; z < 8; z++ ) {
          Location loc(t,z);
          int cell = chipdb->loc_cell(loc); 
          int gate = cell_gate[cell];
          if( gate and locked[gate] ) 
              return std::make_pair(Location(), false);
      }
  }
  
  Location loc( chipdb->tile(new_x, new_y), 0 );
  return std::make_pair(loc, true);
}

void
Placer::move_gate(int gate, int new_cell)
{
  assert(gate);
  if (locked[gate])
    move_failed = true;
  
  int cell = gate_cell[gate]; // copy
  if (new_cell == cell)
    return;
  
  int new_gate = cell_gate[new_cell];
  if (new_gate && locked[new_gate])
    move_failed = true;
  
  save_set(new_cell, gate);
  save_set(cell, new_gate);

#if 0
  Location loc = chipdb->cell_location[cell];
  int t = loc.tile();
  int x = chipdb->tile_x(t), 
      y = chipdb->tile_y(t),
      z = loc.pos();

  *logs << "moving gate from ";
  *logs << cell << "(" << x << "," << y << "," << z << ")";
  loc = chipdb->cell_location[new_cell];
  t = loc.tile();
  x = chipdb->tile_x(t), 
  y = chipdb->tile_y(t),
  z = loc.pos();
  *logs << " to " << new_cell << "(" << x << "," << y << "," << z << ")\n";
#endif
}

void
Placer::move_chain(unsigned c, const Location &new_base)
{
  assert(new_base.pos() == 0);

  /*
  int gate = cell_gate[chipdb->loc_cell(loc)];
  if( locked[gate] )
        return std::make_pair(Location(), false);
  */
  
  int nt = (chains.chains[c].size() + 7) / 8;
  
  int x = chain_x[c];
  int y = chain_y[c];
  
  int new_t = new_base.tile();
  int new_x = chipdb->tile_x(new_t),
      new_y = chipdb->tile_y(new_t);
  if (new_x == x && new_y == y)
    return;

#if 0
  *logs << "moving chain from ";
  *logs << "(" << x << "," << y << ") to ";
  *logs << "(" << new_x << "," << new_y << ")\n";
#endif
  
  for (int i = 0; i < nt; ++i)
    for (unsigned k = 0; k < 8; ++k)
      {
        Location loc(chipdb->tile(x, y + i), k),
          new_loc(chipdb->tile(new_x, new_y + i), k);
        
        int cell = chipdb->loc_cell(loc),
          new_cell = chipdb->loc_cell(new_loc);
        
        unsigned g = cell_gate[cell],
          new_g = cell_gate[new_cell];
        //*logs << "moving gate " << g << " to " << new_cell << "\n";
        //*logs << "moving gate " << new_g << " to " << cell << "\n";
        if (g)
          move_gate(g, new_cell);
        if (new_g)
          move_gate(new_g, cell);
      }
}

int
Placer::tile_n_pos(int t)
{
  switch(chipdb->tile_type[t])
    {
    case TileType::LOGIC:
      return 8;
    case TileType::IO:
      return 2;
    case TileType::RAMT:
      return 1;
    default:
      abort();
      return 0;
    }
}

void
Placer::save_set(int cell, int g)
{
  //*logs << "save_set " << cell << " " << g << "\n";
  const Location &loc = chipdb->cell_location[cell];
  int t = loc.tile();
  
  restore_cell.push_back(std::make_pair(cell, cell_gate[cell]));
  if (g)
    {
      for (int w : gate_nets[g])
        recompute.insert(w);
      gate_cell[g] = cell;
      
      int c = gate_chain[g];
      //*logs << "chain " << g << " " << c << "\n";
      if (c != -1)
        {
          int x = chipdb->tile_x(t),
            y = chipdb->tile_y(t);
          save_set_chain(c, x, y);
        }
    }
  
  cell_gate[cell] = g;
  
  changed_tiles.insert(t);
  for (int t2 : related_tiles[t])
    changed_tiles.insert(t2);
}

void
Placer::save_set_chain(int c, int x, int y)
{
  restore_chain.push_back(std::make_tuple(c, chain_x[c], chain_y[c]));
  //*logs << "chain_x " << x << "; chain_y " << y << "\n";
  chain_x[c] = x;
  chain_y[c] = y;
}

int
Placer::save_recompute_wire_length()
{
  int delta = 0;
  for (int i = 0; i < (int)recompute.size(); ++i)
    {
      int w = recompute.ith(i);
      int new_length = compute_net_length(w),
        old_length = net_length.at(w);
      restore_net_length.push_back(std::make_pair(w, old_length));
      net_length[w] = new_length;
      delta += (new_length - old_length);
    }
  return delta;
}

void
Placer::restore()
{
  move_failed = false;
  for (const auto &p : restore_cell)
    {
      cell_gate[p.first] = p.second;
      if (p.second)
        gate_cell[p.second] = p.first;
    }
  for (const auto &p : restore_net_length)
    net_length[p.first] = p.second;
  for (const auto &t : restore_chain)
    {
      int e, x, y;
      std::tie(e, x, y) = t;
      chain_x[e] = x;
      chain_y[e] = y;
    }
}

void
Placer::discard()
{
  changed_tiles.clear();
  restore_cell.clear();
  restore_chain.clear();
  restore_net_length.clear();
  recompute.clear();
}

bool
Placer::inst_drives_global(Instance *inst, int c, int glb)
{
  Location loc = chipdb->cell_location[c];
  int t = loc.tile();
  int x = chipdb->tile_x(t),
    y = chipdb->tile_y(t);
  if (models.is_gb_io(inst)
      && inst->find_port("GLOBAL_BUFFER_OUTPUT")->connected())
    {
      assert(chipdb->loc_pin_glb_num.at(loc) == glb);
      return true;
    }
  
  if (models.is_gb(inst)
      && inst->find_port("GLOBAL_BUFFER_OUTPUT")->connected())
    {
      assert(chipdb->gbufin.at(std::make_pair(x, y)) == glb);
      return true;
    }
  
  if (models.is_pllX(inst))
    {
      Port *a = inst->find_port("PLLOUTGLOBAL");
      if (!a)
        a = inst->find_port("PLLOUTGLOBALA");
      assert(a);
      if (a->connected())
        {
          const auto &p2 = chipdb->cell_mfvs.at(c).at("PLLOUT_A");
          Location glb_loc(p2.first, std::stoi(p2.second));
          if (chipdb->loc_pin_glb_num.at(glb_loc) == glb)
            return true;
        }
      
      Port *b = inst->find_port("PLLOUTGLOBALB");
      if (b && b->connected())
        {
          const auto &p2 = chipdb->cell_mfvs.at(c).at("PLLOUT_B");
          Location glb_loc(p2.first, std::stoi(p2.second));
          if (chipdb->loc_pin_glb_num.at(glb_loc) == glb)
            return true;
        }
    }
  
  return false;
}

bool
Placer::valid_global(int glb)
{
  int n = 0;
  for (int c : global_cells.at(glb))
    {
      int g = cell_gate[c];
      if (!g)
        continue;
      Instance *inst = gates[g];
      if (inst_drives_global(inst, c, glb))
        {
          if (n > 0)
            return false;
          ++n;
        }
    }
  return true;
}

bool
Placer::valid(int t)
{
  int x = chipdb->tile_x(t),
      y = chipdb->tile_y(t);
  if (chipdb->tile_type[t] == TileType::LOGIC) {
      int global_clk = 0,
          global_sr = 0,
          global_cen = 0;
      int neg_clk = -1;
      tmp_local_np.clear();
      for (int q = 0; q < 8; q ++) {
          Location loc(t, q);
          int cell = chipdb->loc_cell(loc);
          int g = cell_gate[cell];
          if (g) {
              Instance *inst = gates[g];
              
              int clk = gate_clk[g],
                   sr = gate_sr[g],
                  cen = gate_cen[g];
              
              if (!global_clk)
                global_clk = clk;
              else if (global_clk != clk)
                return false;
              
              if (!global_sr)
                global_sr = sr;
              else if (global_sr != sr)
                return false;
              
              if (!global_cen)
                global_cen = cen;
              else if (global_cen != cen)
                return false;
              
              int g_neg_clk = (int)inst->get_param("NEG_CLK").get_bit(0);
              if (neg_clk == -1)
                neg_clk = g_neg_clk;
              else if (neg_clk != g_neg_clk)
                return false;
              
              for (int np : gate_local_np[g])
                tmp_local_np.insert(np ^ (q & 1));
            }
        }
      
      if (global_clk
          && !net_global[global_clk])
        tmp_local_np.insert(global_clk << 1);
      if (global_sr
          && !net_global[global_sr])
        tmp_local_np.insert(global_sr << 1);
      if (global_cen
          && !net_global[global_cen])
        tmp_local_np.insert(global_cen << 1);
      
      if (tmp_local_np.size() > 29)
        return false;
    }
  else if (chipdb->tile_type[t] == TileType::IO)
    {
      int b = chipdb->tile_bank(t);
      
      int latch = 0;
      for (int cell : chipdb->bank_cells[b]) {
          int g = cell_gate[cell];
          if (g)
            {
              int n = gate_latch[g];
              if (latch)
                {
                  if (latch != n)
                    return false;
                }
              else
                latch = n;
            }
        }
      
      Location loc0(t, 0),
        loc1(t, 1);
      int cell0 = chipdb->loc_cell(loc0),
        cell1 = chipdb->loc_cell(loc1);
      int g0 = cell0 ? cell_gate[cell0] : 0,
        g1 = cell1 ? cell_gate[cell1] : 0;
      if (g0)
        {
          if (!contains(package.loc_pin, loc0))
            return false;
          
          Instance *inst0 = gates[g0];
          if (inst0->get_param("IO_STANDARD").as_string() == "SB_LVDS_INPUT")
            {
              if (b != 3)
                return false;
              if (g1)
                return false;
            }
          if (models.is_gb_io(inst0)
              && inst0->find_port("GLOBAL_BUFFER_OUTPUT")->connected())
            {
              int glb = chipdb->loc_pin_glb_num.at(loc0);
              if (!valid_global(glb))
                return false;
            }
        }
      if (g1)
        {
          if (!contains(package.loc_pin, loc1))
            return false;
          
          Instance *inst1 = gates[g1];
          if (inst1->get_param("IO_STANDARD").as_string() == "SB_LVDS_INPUT")
            return false;
          if (models.is_gb_io(inst1)
              && inst1->find_port("GLOBAL_BUFFER_OUTPUT")->connected())
            {
              int glb = chipdb->loc_pin_glb_num.at(loc1);
              if (!valid_global(glb))
                return false;
            }
        }
      
      if (g0 && g1)
        {
          Instance *inst0 = gates[g0],
            *inst1 = gates[g1];
          if (inst0->get_param("NEG_TRIGGER").get_bit(0)
              != inst1->get_param("NEG_TRIGGER").get_bit(0))
            return false;
          
          Net *cen0 = inst0->find_port("CLOCK_ENABLE")->connection(),
            *cen1 = inst1->find_port("CLOCK_ENABLE")->connection();
          if (cen0 && cen1 && cen0 != cen1)
            return false;
          
          Net *inclk0 = inst0->find_port("INPUT_CLK")->connection(),
            *inclk1 = inst1->find_port("INPUT_CLK")->connection();
          if (inclk0 && inclk1 && inclk0 != inclk1)
            return false;
          
          Net *outclk0 = inst0->find_port("OUTPUT_CLK")->connection(),
            *outclk1 = inst1->find_port("OUTPUT_CLK")->connection();
          if (outclk0 && outclk1 && outclk0 != outclk1)
            return false;
        }
      
      Location loc2(t, 2);
      int cell2 = chipdb->loc_cell(loc2);
      int g2 = cell2 ? cell_gate[cell2] : 0;
      if (g2)
        {
          if ((g0 && models.is_gb_io(gates[g0]))
              || (g1 && models.is_gb_io(gates[g1])))
            return false;
          
          Instance *inst = gates[g2];
          int gc = lookup_or_default(gb_inst_gc, inst, gc_clk);
          int glb = chipdb->gbufin.at(std::make_pair(x, y));
          if (! (gc & (1 << glb)))
            return false;
          if (!valid_global(glb))
            return false;
        }
      
      Location loc3(t, 3);
      int cell3 = chipdb->loc_cell(loc3);
      int g3 = cell3 ? cell_gate[cell3] : 0;
      Instance *inst3 = g3 ? gates[g3] : nullptr;
      if (inst3)
        {
          Port *pa = inst3->find_port("PLLOUTGLOBAL");
          if (!pa)
            pa = inst3->find_port("PLLOUTGLOBALA");
          assert(pa);
          if (pa->connected())
            {
              const auto &p2 = chipdb->cell_mfvs.at(cell3).at("PLLOUT_A");
              Location glb_loc(p2.first, std::stoi(p2.second));
              int glb = chipdb->loc_pin_glb_num.at(glb_loc);
              if (!valid_global(glb))
                return false;
            }
          
          Port *pb = inst3->find_port("PLLOUTGLOBALB");
          if (pb && pb->connected())
            {
              const auto &p2 = chipdb->cell_mfvs.at(cell3).at("PLLOUT_B");
              Location glb_loc(p2.first, std::stoi(p2.second));
              int glb = chipdb->loc_pin_glb_num.at(glb_loc);
              if (!valid_global(glb))
                return false;
            }
          
          const auto &pA = chipdb->cell_mfvs.at(cell3).at("PLLOUT_A");
          int tA = pA.first;
          int iA = std::stoi(pA.second);
          
          int cA = chipdb->loc_cell(Location(tA, iA));
          int gA = cell_gate[cA];
          Instance *instA = gA ? gates[gA] : nullptr;
          
          if (instA && instA->find_port("D_IN_0")->connection())
            return false;
          
          if (inst3->instance_of()->name() == "SB_PLL40_2F_CORE"
              || inst3->instance_of()->name() == "SB_PLL40_2_PAD"
              || inst3->instance_of()->name() == "SB_PLL40_2F_PAD")
            {
              const auto &pB = chipdb->cell_mfvs.at(cell3).at("PLLOUT_B");
              int tB = pB.first;
              int iB = std::stoi(pB.second);
          
              int cB = chipdb->loc_cell(Location(tB, iB));
              int gB = cell_gate[cB];
              Instance *instB = gB ? gates[gB] : nullptr;
          
              if (instB && instB->find_port("D_IN_0")->connection())
                return false;
            }
        }
    }
  else
    assert(chipdb->tile_type[t] == TileType::RAMT);
  
  return true;
}

void
Placer::accept_or_restore()
{
  int delta;

  if (move_failed)
    goto L;
  for (int i = 0; i < (int)changed_tiles.size(); ++i)
    {
      int t = changed_tiles.ith(i);
      if (!valid(t))
        goto L;
    }
  
  delta = save_recompute_wire_length();
  
  // check();
  
  ++n_move;
  if (delta < 0
      || (temp > 1e-6
          && rg.random_real(0.0, 1.0) <= exp(-delta/temp)))
    {
      if (delta < 0)
        {
          // std::cout << "delta " << delta << "\n";
          improved = true;
        }
      //*logs << "move accepted: wire length " << wire_length() << "\n";
      ++n_accept;
    }
  else
    {
    L:
      restore();
    }
  discard();
  
  // check();
}

unsigned
Placer::top_port_io_gate(const std::string &net_name)
{
  Port *p = top->find_port(net_name);
  assert(p);
  
  Port *p2 = p->connection_other_port();
  
  Instance *inst = cast<Instance>(p2->node());
  assert(models.is_io(inst));
  
  return gate_idx.at(inst);
}

#ifndef NDEBUG
void
Placer::check()
{
  // for (int g = 1; g <= n_gates; ++g)
  for (Instance *inst : top->instances())
    {
      int g = gate_idx.at(inst);
      assert(cell_gate[gate_cell[g]] == g);
    }
  for (int i = 1; i <= chipdb->n_cells; ++i)
    {
      int g = cell_gate[i];
      if (g)
        assert(gate_cell[g] == i);
    }
  
  for (unsigned c = 0; c < chains.chains.size(); ++c)
    {
      const auto &v = chains.chains[c];
      for (unsigned i = 0; i < v.size(); ++i)
        {
          Location loc (chipdb->tile(chain_x[c],
                                     chain_y[c] + i / 8),
                        i % 8);
          int g = gate_idx.at(v[i]);
          int cell = chipdb->loc_cell(loc);
          int cell_g = cell_gate[cell];
          assert(g == cell_g);
        }
      
      int nt = (v.size() + 7) / 8;
      int y = chain_y[c];
      assert(y + nt - 1 <= chipdb->height - 2);
    }
  for (int w = 1; w < (int)nets.size(); ++w) // skip 0, nullptr
    assert(net_length[w] == compute_net_length(w));
}
#endif

int
Placer::compute_net_length(int w)
{
  if (net_global[w]
      || net_gates[w].empty())
    return 0;
  
  const std::vector<int> &w_gates = net_gates[w];
  
  int g0 = w_gates[0];
  int cell0 = gate_cell[g0];
  const Location &loc0 = chipdb->cell_location[cell0];
  int t0 = loc0.tile();
  int x_min = chipdb->tile_x(t0),
    x_max = chipdb->tile_x(t0),
    y_min = chipdb->tile_y(t0),
    y_max = chipdb->tile_y(t0);
  
  for (int i = 1; i < (int)w_gates.size(); ++i)
    {
      int g = w_gates[i];
      int cell = gate_cell[g];
      const Location &loc = chipdb->cell_location[cell];
      int t = loc.tile();
      int x = chipdb->tile_x(t),
        y = chipdb->tile_y(t);
      x_min = std::min(x_min, x);
      x_max = std::max(x_max, x);
      y_min = std::min(y_min, y);
      y_max = std::max(y_max, y);
    }
  
  assert(x_min <= x_max && y_min <= y_max);
  return (x_max - x_min) + (y_max - y_min);
}

int
Placer::wire_length() const
{
  int length = 0;
  for (int ell : net_length)
    length += ell;
  return length;
}

Placer::Placer(random_generator &rg_, DesignState &ds_)
  : rg(rg_),
    ds(ds_),
    chipdb(ds.chipdb),
    package(ds.package),
    d(ds.d),
    models(ds.models),
    top(ds.top),
    chains(ds.chains),
    constraints(ds.constraints),
    gb_inst_gc(ds.gb_inst_gc),
    placement(ds.placement),
    conf(ds.conf),
    related_tiles(chipdb->n_tiles),
    diameter(std::max(chipdb->width,
                      chipdb->height)),
    temp(10000.0),
    move_failed(false),
    changed_tiles(chipdb->n_tiles),
    cell_gate(chipdb->n_cells, 0)
{

  for (const auto &p : chipdb->loc_pin_glb_num)
    {
      const Location &loc = p.first;
      int c = chipdb->loc_cell(loc);
      int glb = p.second;
      global_cells[glb].push_back(c);
    }
  for (const auto &p : chipdb->gbufin)
    {
      int x = p.first.first,
          y = p.first.second;
      int glb = p.second;
      int t = chipdb->tile(x, y);
      Location loc(t, 2);
      int c = chipdb->loc_cell(loc);
      global_cells[glb].push_back(c);
    }
  
  for (int i = 1; i <= (int)chipdb->n_cells; ++i)
    {
      // FIXME
      if (chipdb->cell_type[i] == CellType::PLL)
        {
          int t = chipdb->cell_location[i].tile();
          
          // global_cells
          const auto &p2a = chipdb->cell_mfvs.at(i).at("PLLOUT_A");
          Location glb_loca(p2a.first, std::stoi(p2a.second));
          int glba = chipdb->loc_pin_glb_num.at(glb_loca);
          global_cells[glba].push_back(i);
          
          const auto &p2b = chipdb->cell_mfvs.at(i).at("PLLOUT_B");
          Location glb_locb(p2b.first, std::stoi(p2b.second));
          int glbb = chipdb->loc_pin_glb_num.at(glb_locb);
          global_cells[glbb].push_back(i);
          
          // related tiles
          std::vector<int> t_related;
          t_related.push_back(t);
          
          const auto &pA = chipdb->cell_mfvs.at(i).at("PLLOUT_A");
          int tA = pA.first;
          t_related.push_back(tA);
          
          const auto &pB = chipdb->cell_mfvs.at(i).at("PLLOUT_B");
          int tB = pB.first;
          t_related.push_back(tB);
          
          for (int t2 : t_related)
            related_tiles[t2] = t_related;
        }
    }
  
  // initialize list of columns containing logic cells
  for (int i = 0; i < chipdb->width; ++i)
    {
      int t = chipdb->tile(i, 1);
      if (chipdb->tile_type[t] == TileType::LOGIC)
        logic_columns.push_back(i);
    }

  // initialize tile lists of different types
  for (int i = 0; i < chipdb->n_tiles; ++i)
    {
        switch(chipdb->tile_type[i])
        {
        case TileType::LOGIC:
          logic_tiles.push_back(i);
          break;
        case TileType::RAMT:
          ramt_tiles.push_back(i);
          break;
        default:
          break;
        }
    }


  std::tie(nets, net_idx) = top->index_nets();
  int n_nets = nets.size();
  
  net_global.resize(n_nets);
  
  net_length.resize(n_nets);
  net_gates.resize(n_nets);
  recompute.resize(n_nets);
  
  std::tie(gates, gate_idx) = top->index_instances();
  n_gates = gates.size();
  
  gate_clk.resize(n_gates, 0);
  gate_sr.resize(n_gates, 0);
  gate_cen.resize(n_gates, 0);
  gate_latch.resize(n_gates, 0);
  gate_local_np.resize(n_gates);
  tmp_local_np.resize(n_nets * 2);
  gate_chain.resize(n_gates, -1);
  
  gate_cell.resize(n_gates);
  gate_nets.resize(n_gates);
  
  for (int i = 1; i <= n_gates; ++i)
    {
      Instance *inst = gates[i];
      if (models.is_lc(inst))
        {
          Net *clk = inst->find_port("CLK")->connection();
          if (clk)
            gate_clk[i] = net_idx.at(clk);
          
          Net *sr = inst->find_port("SR")->connection();
          if (sr)
            gate_sr[i] = net_idx.at(sr);
          
          Net *cen = inst->find_port("CEN")->connection();
          if (cen)
            gate_cen[i] = net_idx.at(cen);
          
          tmp_local_np.clear();
          for (int j = 0; j < 4; ++j)
            {
              Net *n = inst->find_port(fmt("I" << j))->connection();
              if (n
                  && !n->is_constant())
                tmp_local_np.insert((net_idx.at(n) << 1) | (j & 1));
            }
          
          for (int j = 0; j < (int)tmp_local_np.size(); ++j)
            gate_local_np[i].push_back(tmp_local_np.ith(j));
        }
      else if (models.is_io(inst))
        {
          Net *latch = inst->find_port("LATCH_INPUT_VALUE")->connection();
          if (latch)
            gate_cen[i] = net_idx.at(latch);
        }
      else if (models.is_gb(inst))
        {
          Net *n = inst->find_port("GLOBAL_BUFFER_OUTPUT")->connection();
          if (n)
            net_global[net_idx.at(n)] = true;
        }
    }

}

/*
 * alloc unused cell from list of empty cells
 */
int 
Placer::alloc_cell(CellType celltype, int gate)
{
    int ct_idx = cell_type_idx(celltype);
    auto &v = cell_type_empty_cells[ct_idx];
          
    for (int j = 0; j < (int)v.size(); ++j) {
        int cell = v[j];
              
        // should not have been used
        assert(cell_gate[cell] == 0);

        // check whether this gate can be placed on this cell
        cell_gate[cell] = gate; //gate_cell[gate] = cell;
        if( valid(chipdb->cell_location[cell].tile())) {
            cell_gate[cell] = 0;
            pop(v, j); // remove from empty list
            return cell;
        }
        cell_gate[cell] = 0; //gate_cell[gate] = 0;
    }
    fatal(fmt("failed to place: placed " << cell_type_name(celltype)));
    return 0;
}

/*
 * return true if all the cells in this tile are unused
 */
bool 
Placer::free_tile(int x, int y)
{
    for( int z = 0; z < 8; z++ ) {
        Location loc(chipdb->tile(x, y), z);
        if( cell_gate[chipdb->loc_cell(loc)] != 0)
             return false;
    }
    return true;
}

/*
 * return true if nt tiles starting at x, y are unused
 */
bool 
Placer::free_tiles(int x, int y, int nt)
{
    int y_end = y + nt;
    while( y < y_end ) {
        if( !free_tile(x, y) )
            return false;
        y++;
    }
    return true;
}

/*
 * find first block of nt free tiles starting y in column x
 */
int
Placer::find_free_tiles(int x, int nt)
{
    for( int y = 1; y < chipdb->height - 1; y++ )
        if( free_tiles( x, y, nt ) )
            return y;
    return 0;
}

/*
 * alloc nt unused tiles
 */
int 
Placer::alloc_tiles(int nt)
{
    int x = 0;
    int y = 0;
    for (unsigned k = 0; k < logic_columns.size(); ++k) {
        x = logic_columns[k];
        y = find_free_tiles(x, nt);
        if( y != 0 )
            break;
    }
    assert( y != 0 );
    *logs << "found tile at " << x << "," << y <<"\n";
    return chipdb->tile(x, y);
}

/*
 * place gate at cell
 *  set chained and locked for that gate
 */
void
Placer::place_gate(int gate, int cell, bool chain, bool lock)
{
#if 0
    Location loc = chipdb->cell_location[cell];
    int t = loc.tile();
    int x = chipdb->tile_x(t),
        y = chipdb->tile_y(t),
        z = loc.pos();

    *logs << "placing ";
    if( lock ) 
        *logs << "locked ";
    if( chain )
        *logs << "chained ";
    *logs << "gate " << gate << " at cell " << cell << " (" << x << "," << y << "," << z << ")\n";
#endif

    // assert that this cell is unused
    assert(cell_gate[cell] == 0);

    cell_gate[cell] = gate;
    gate_cell[gate] = cell;

    chained[gate] = chain;
    locked[gate] = lock;

    assert(valid(chipdb->cell_location[cell].tile()));
}

void
Placer::place_chain(const std::vector<Instance*> &v, int t, bool lock)
{
    int x = chipdb->tile_x(t);
    int y = chipdb->tile_y(t);
    for (unsigned j = 0; j < v.size(); ++j) {
        Location loc(chipdb->tile(x, y + j / 8), j % 8);
        int cell = chipdb->loc_cell(loc);
        place_gate(gate_idx.at(v[j]), cell,  true, lock);
    }

    // save location of chain
    chain_x.push_back(x);
    chain_y.push_back(y);
#if 0
    *logs << "placing ";
    if( lock ) 
        *logs << "locked ";
    *logs << "chain " << " at tile " << t << "(" << x << "," << y << ")\n";
#endif
}

void
Placer::place_initial()
{
    locked.resize(n_gates);
    chained.resize(n_gates);

    // count number of gates of each cell type
    std::vector<int> cell_type_n_gates(n_cell_types, 0);
    for (int g = 1; g <= n_gates; ++g)
        ++cell_type_n_gates[cell_type_idx(gate_cell_type(g))];

    // count of the number of cells placed
    std::vector<int> cell_type_n_placed(n_cell_types, 0);

    *logs << "placing gates in placement list\n";
    for (const auto &p : placement) {
        Instance *inst = p.first;
        int gate = gate_idx.at(inst);
        int cell = p.second;
      
        place_gate(gate, cell, false, true);
      
        ++cell_type_n_placed[cell_type_idx(gate_cell_type(gate))];
    }

    *logs << "placing chains ... \n"; 
    for (unsigned i = 0; i < chains.chains.size(); ++i) {
        const auto &v = chains.chains[i];
      
        CellType ct = gate_cell_type(gate_idx.at(v[0]));
        if ((ct != CellType::LOGIC) || (v[0]->has_attr("loc")))
            continue;

        int gate0 = gate_idx.at(v[0]);
        if( gate_cell[gate0] != 0 ) // already placed
            continue;

        // assert that no other chain begins here
        assert(gate_chain[gate0] == -1);
        gate_chain[gate0] = i;

        int nt = (v.size() + 7) / 8;
        int t = alloc_tiles(nt);

        place_chain(v, t, false);

        cell_type_n_placed[cell_type_idx(ct)] += v.size();
    }
  
    // initialize empty cell lists to all chipdb cells
    cell_type_empty_cells = chipdb->cell_type_cells;

    // remove cells from the empty cell lists if they been assigned 
    for (int i = 0; i < n_cell_types; ++i)
        for (int j = 0; j < (int)cell_type_empty_cells[i].size();) {
            int c = cell_type_empty_cells[i][j];
            // if the cell has been placed, remove it from the empty cell list
            if (cell_gate[c] != 0)
                pop(cell_type_empty_cells[i], j);
            else
                ++j;
      }
  
    *logs << "placing cells ...\n"; // (except GB and WARMBOOT)
    for (int g = 1; g <= n_gates; ++g) {
        CellType celltype = gate_cell_type(g);
        if ((celltype == CellType::WARMBOOT) || (celltype == CellType::GB))
            continue;
        if( gate_cell[g] != 0 ) // placed
            continue;
        assert(!locked[g]);
        assert(!chained[g]);
      
        // free_gates are gates that can be moved during the place process
        free_gates.push_back(g);

        int c = alloc_cell(celltype, g);

        place_gate(g, c, false, false);

        ++cell_type_n_placed[cell_type_idx(celltype)];
    }

    // this seems weird
    *logs << "placing GB\n"; // (except WARMBOOT)
    for (int g = 1; g <= n_gates; ++g) {
        CellType celltype = gate_cell_type(g);
        if ((celltype == CellType::WARMBOOT) || (celltype != CellType::GB))
            continue;
        if( gate_cell[g] != 0 ) // placed
            continue;
        assert(!locked[g]);
        assert(!chained[g]);
      
        // free_gates are gates that can be moved during the place process
        free_gates.push_back(g);

        int c = alloc_cell(celltype, g);

        place_gate(g, c, false, false);

        ++cell_type_n_placed[cell_type_idx(celltype)];
    }

    // net stuff

    for (int g = 1; g <= n_gates; ++g) {
        Instance *inst = gates[g];
        for (const auto &p : inst->ports()) {
            Net *n = p.second->connection();
            if (n
              && !n->is_constant())  // constants are not routed
            {
              int w = net_idx.at(n);
              net_gates[w].push_back(g);
              gate_nets[g].push_back(w);
            }
        }
    }
  
    for (int w = 0; w < (int)nets.size(); ++w)
        net_length[w] = compute_net_length(w);
}

void
Placer::configure_io(const Location &loc,
                     bool enable_input,
                     bool pullup)
{
  const auto &func_cbits = chipdb->tile_nonrouting_cbits.at(TileType::IO);
  const CBit &ie_0 = func_cbits.at("IoCtrl.IE_0")[0],
    &ie_1 = func_cbits.at("IoCtrl.IE_1")[0],
    &ren_0 = func_cbits.at("IoCtrl.REN_0")[0],
    &ren_1 = func_cbits.at("IoCtrl.REN_1")[0];
  
  if (loc.pos() == 0)
    {
      conf.set_cbit(CBit(loc.tile(),
                         ren_0.row,
                         ren_0.col),
                    !pullup);  // active low
    }
  else
    {
      assert(loc.pos() == 1);
      conf.set_cbit(CBit(loc.tile(),
                         ren_1.row,
                         ren_1.col),
                    !pullup);  // active low
    }
  if (loc.pos() == 0)
    {
      conf.set_cbit(CBit(loc.tile(),
                         ie_0.row,
                         ie_0.col),
                    // active low 1k, active high 8k
                    (chipdb->device == "1k"
                     ? !enable_input
                     : enable_input));
    }
  else
    {
      assert(loc.pos() == 1);
      conf.set_cbit(CBit(loc.tile(),
                         ie_1.row,
                         ie_1.col),
                    // active low 1k, active high 8k
                    (chipdb->device == "1k"
                     ? !enable_input
                     : enable_input));
    }
}

void
Placer::configure()
{
  for (int g = 1; g <= n_gates; g ++)
    {
      Instance *inst = gates[g];
      int cell = gate_cell[g];

      const Location &loc = chipdb->cell_location[cell];
      int t = loc.tile();
      
      /*
      int x = chipdb->tile_x(t),
          y = chipdb->tile_y(t),
          z = loc.pos();
      *logs << "gate " << g << " at cell " << cell << " (" << x << "," << y << "," << z << ")\n";
      */
      
      
      if (models.is_warmboot(inst)) {
        placement[inst] = cell;
        continue;
      }

      const auto &func_cbits = chipdb->tile_nonrouting_cbits.at(chipdb->tile_type[t]);
      
      if (models.is_lc(inst))
        {
          BitVector lut_init = inst->get_param("LUT_INIT").as_bits();
          lut_init.resize(16);
          
          static std::vector<int> lut_perm = {
            4, 14, 15, 5, 6, 16, 17, 7, 3, 13, 12, 2, 1, 11, 10, 0,
          };
          
          const auto &cbits = func_cbits.at(fmt("LC_" << loc.pos()));
          for (int i = 0; i < 16; ++i)
            conf.set_cbit(CBit(t,
                               cbits[lut_perm[i]].row,
                               cbits[lut_perm[i]].col),
                          lut_init[i]);
          
          bool carry_enable = inst->get_param("CARRY_ENABLE").get_bit(0);
          if (carry_enable)
            {
              conf.set_cbit(CBit(t,
                                 cbits[8].row,
                                 cbits[8].col), (bool)carry_enable);
              if (loc.pos() == 0)
                {
                  Net *n = inst->find_port("CIN")->connection();
                  if (n && n->is_constant())
                    {
                      const CBit &carryinset_cbit = func_cbits.at("CarryInSet")[0];
                      conf.set_cbit(CBit(t,
                                         carryinset_cbit.row,
                                         carryinset_cbit.col), 
                                    n->constant() == Value::ONE);
                    }
                }
            }
          
          bool dff_enable = inst->get_param("DFF_ENABLE").get_bit(0);
          conf.set_cbit(CBit(t,
                             cbits[9].row,
                             cbits[9].col), dff_enable);
          
          if (dff_enable)
            {
              bool neg_clk = inst->get_param("NEG_CLK").get_bit(0);
              const CBit &neg_clk_cbit = func_cbits.at("NegClk")[0];
              conf.set_cbit(CBit(t,
                                 neg_clk_cbit.row,
                                 neg_clk_cbit.col),
                            (bool)neg_clk);
              
              bool set_noreset = inst->get_param("SET_NORESET").get_bit(0);
              conf.set_cbit(CBit(t,
                                 cbits[18].row,
                                 cbits[18].col), (bool)set_noreset);
              
              bool async_sr = inst->get_param("ASYNC_SR").get_bit(0);
              conf.set_cbit(CBit(t,
                                 cbits[19].row,
                                 cbits[19].col), (bool)async_sr);
            }
        }
      else if (models.is_ioX(inst))
        {
          assert(contains(package.loc_pin, loc));
          
          const BitVector &pin_type = inst->get_param("PIN_TYPE").as_bits();
          for (int i = 0; i < 6; ++i)
            {
              const CBit &cbit = func_cbits.at(fmt("IOB_" << loc.pos() << ".PINTYPE_" << i))[0];
              conf.set_cbit(CBit(t, 
                                 cbit.row, 
                                 cbit.col),
                            pin_type[i]);
            }
          
          const auto &negclk_cbits = func_cbits.at("NegClk");
          bool neg_trigger = inst->get_param("NEG_TRIGGER").get_bit(0);
          for (int i = 0; i <= 1; ++i)
            conf.set_cbit(CBit(t,
                               negclk_cbits[i].row,
                               negclk_cbits[i].col),
                          neg_trigger);
          
          if (models.is_gb_io(inst)
              && inst->find_port("GLOBAL_BUFFER_OUTPUT")->connected())
            {
              int glb = chipdb->loc_pin_glb_num.at(loc);
              
              const auto &ecb = chipdb->extra_bits.at(fmt("padin_glb_netwk." << glb));
              conf.set_extra_cbit(ecb);
            }
        }
      else if (models.is_gb(inst))
        ;
      else if (models.is_ramX(inst))
        {
          BitVector wm = inst->get_param("WRITE_MODE").as_bits(),
            rm = inst->get_param("READ_MODE").as_bits();
          wm.resize(2);
          rm.resize(2);
          
          // powerup active low, don't set
          const auto &ramb_func_cbits = chipdb->tile_nonrouting_cbits.at(TileType::RAMB);
          const CBit &cbit0 = func_cbits.at("RamConfig.CBIT_0")[0],
            &cbit1 = func_cbits.at("RamConfig.CBIT_1")[0],
            &cbit2 = func_cbits.at("RamConfig.CBIT_2")[0],
            &cbit3 = func_cbits.at("RamConfig.CBIT_3")[0],
            &negclk = func_cbits.at("NegClk")[0],
            &ramb_negclk = ramb_func_cbits.at("NegClk")[0];
          
          conf.set_cbit(CBit(t,
                             cbit0.row,
                             cbit0.col),
                        wm[0]);
          conf.set_cbit(CBit(t,
                             cbit1.row,
                             cbit1.col),
                        wm[1]);
          conf.set_cbit(CBit(t,
                             cbit2.row,
                             cbit2.col),
                        rm[0]);
          conf.set_cbit(CBit(t,
                             cbit3.row,
                             cbit3.col),
                        rm[1]);
          
          if (models.is_ramnr(inst)
              || models.is_ramnrnw(inst))
            conf.set_cbit(CBit(t,
                               negclk.row,
                               negclk.col),
                          true);
          
          if (models.is_ramnw(inst)
              || models.is_ramnrnw(inst))
            conf.set_cbit(CBit(chipdb->ramt_ramb_tile(t),
                               ramb_negclk.row,
                               ramb_negclk.col),
                          true);
        }
      else
        {
          assert(models.is_pllX(inst));
          
          bool found = false;
          Location io_loc;
          for (const auto &p2 : chipdb->loc_pin_glb_num)
            {
              if (p2.first.tile() == t)
                {
                  assert(!found);
                  io_loc = p2.first;
                  found = true;
                }
            }
          assert(found);
          
          const CBit &cbit_pt0 = func_cbits.at(fmt("IOB_" << io_loc.pos() << ".PINTYPE_0"))[0],
            &cbit_pt1 = func_cbits.at(fmt("IOB_" << io_loc.pos() << ".PINTYPE_1"))[0];
          
          conf.set_cbit(CBit(t, 
                             cbit_pt0.row, 
                             cbit_pt0.col),
                        true);
          conf.set_cbit(CBit(t, 
                             cbit_pt1.row, 
                             cbit_pt1.col),
                        false);
          
          CBit delay_adjmode_fb_cb = chipdb->extra_cell_cbit(cell, "DELAY_ADJMODE_FB");
          
          std::string delay_adjmode_fb = inst->get_param("DELAY_ADJUSTMENT_MODE_FEEDBACK").as_string();
          if (delay_adjmode_fb == "FIXED")
            conf.set_cbit(delay_adjmode_fb_cb, false);
          else if (delay_adjmode_fb == "DYNAMIC")
            conf.set_cbit(delay_adjmode_fb_cb, true);
          else
            fatal(fmt("unknown DELAY_ADJUSTMENT_MODE_FEEDBACK value: " << delay_adjmode_fb));
          
          CBit delay_adjmode_rel_cb = chipdb->extra_cell_cbit(cell, "DELAY_ADJMODE_REL");
          
          std::string delay_adjmode_rel = inst->get_param("DELAY_ADJUSTMENT_MODE_RELATIVE").as_string();
          if (delay_adjmode_rel == "FIXED")
            conf.set_cbit(delay_adjmode_rel_cb, false);
          else if (delay_adjmode_rel == "DYNAMIC")
            conf.set_cbit(delay_adjmode_rel_cb, true);
          else
            fatal(fmt("unknown DELAY_ADJUSTMENT_MODE_RELATIVE value: " << delay_adjmode_rel));
          
          BitVector divf = inst->get_param("DIVF").as_bits();
          divf.resize(7);
          for (int i = 0; i < (int)divf.size(); ++i)
            {
              CBit divf_i_cb = chipdb->extra_cell_cbit(cell, fmt("DIVF_" << i));
              conf.set_cbit(divf_i_cb, divf[i]);
            }
          
          BitVector divq = inst->get_param("DIVQ").as_bits();
          divq.resize(3);
          for (int i = 0; i < (int)divq.size(); ++i)
            {
              CBit divq_i_cb = chipdb->extra_cell_cbit(cell, fmt("DIVQ_" << i));
              conf.set_cbit(divq_i_cb, divq[i]);
            }
          
          BitVector divr = inst->get_param("DIVR").as_bits();
          divr.resize(4);
          for (int i = 0; i < (int)divr.size(); ++i)
            {
              CBit divr_i_cb = chipdb->extra_cell_cbit(cell, fmt("DIVR_" << i));
              conf.set_cbit(divr_i_cb, divr[i]);
            }
          
          BitVector fda_feedback = inst->get_param("FDA_FEEDBACK").as_bits();
          fda_feedback.resize(4);
          for (int i = 0; i < (int)fda_feedback.size(); ++i)
            {
              CBit fda_feedback_i_cb = chipdb->extra_cell_cbit(cell, fmt("FDA_FEEDBACK_" << i));
              conf.set_cbit(fda_feedback_i_cb, fda_feedback[i]);
            }
          
          BitVector fda_relative = inst->get_param("FDA_RELATIVE").as_bits();
          fda_relative.resize(4);
          for (int i = 0; i < (int)fda_relative.size(); ++i)
            {
              CBit fda_relative_i_cb = chipdb->extra_cell_cbit(cell, fmt("FDA_RELATIVE_" << i));
              conf.set_cbit(fda_relative_i_cb, fda_relative[i]);
            }
          
          std::string feedback_path_str = inst->get_param("FEEDBACK_PATH").as_string();
          
          int feedback_path_value = 0;
          if (feedback_path_str == "DELAY")
            feedback_path_value = 0;
          else if (feedback_path_str == "SIMPLE")
            feedback_path_value = 1;
          else if (feedback_path_str == "PHASE_AND_DELAY")
            feedback_path_value = 2;
          else
            {
              assert(feedback_path_str == "EXTERNAL");
              feedback_path_value = 6;
            }
          
          BitVector feedback_path(3, feedback_path_value);
          for (int i = 0; i < (int)feedback_path.size(); ++i)
            {
              CBit feedback_path_i_cb = chipdb->extra_cell_cbit(cell, fmt("FEEDBACK_PATH_" << i));
              conf.set_cbit(feedback_path_i_cb, feedback_path[i]);
            }
          
          BitVector filter_range = inst->get_param("FILTER_RANGE").as_bits();
          filter_range.resize(3);
          for (int i = 0; i < (int)filter_range.size(); ++i)
            {
              CBit filter_range_i_cb = chipdb->extra_cell_cbit(cell, fmt("FILTER_RANGE_" << i));
              conf.set_cbit(filter_range_i_cb, filter_range[i]);
            }
          
          std::string pllout_select_porta_str;
          if (inst->instance_of()->name() == "SB_PLL40_PAD"
              || inst->instance_of()->name() == "SB_PLL40_CORE")
            pllout_select_porta_str = inst->get_param("PLLOUT_SELECT").as_string();
          else
            pllout_select_porta_str = inst->get_param("PLLOUT_SELECT_PORTA").as_string();
          
          int pllout_select_porta_value = 0;
          if (pllout_select_porta_str == "GENCLK")
            pllout_select_porta_value = 0;
          else if (pllout_select_porta_str == "GENCLK_HALF")
            pllout_select_porta_value = 1;
          else if (pllout_select_porta_str == "SHIFTREG_90deg")
            pllout_select_porta_value = 2;
          else
            {
              assert(pllout_select_porta_str == "SHIFTREG_0deg");
              pllout_select_porta_value = 3;
            }
          
          BitVector pllout_select_porta(2, pllout_select_porta_value);
          for (int i = 0; i < (int)pllout_select_porta.size(); ++i)
            {
              CBit pllout_select_porta_i_cb = chipdb->extra_cell_cbit(cell, fmt("PLLOUT_SELECT_A_" << i));
              conf.set_cbit(pllout_select_porta_i_cb, pllout_select_porta[i]);
            }
          
          int pllout_select_portb_value = 0;
          if (inst->instance_of()->name() == "SB_PLL40_2_PAD"
              || inst->instance_of()->name() == "SB_PLL40_2F_PAD"
              || inst->instance_of()->name() == "SB_PLL40_2F_CORE")
            {
              std::string pllout_select_portb_str = inst->get_param("PLLOUT_SELECT_PORTB").as_string();
              
              if (pllout_select_portb_str == "GENCLK")
                pllout_select_portb_value = 0;
              else if (pllout_select_portb_str == "GENCLK_HALF")
                pllout_select_portb_value = 1;
              else if (pllout_select_portb_str == "SHIFTREG_90deg")
                pllout_select_portb_value = 2;
              else
                {
                  assert(pllout_select_portb_str == "SHIFTREG_0deg");
                  pllout_select_portb_value = 3;
                }
            }
          
          BitVector pllout_select_portb(2, pllout_select_portb_value);
          for (int i = 0; i < (int)pllout_select_portb.size(); ++i)
            {
              CBit pllout_select_portb_i_cb = chipdb->extra_cell_cbit(cell, fmt("PLLOUT_SELECT_B_" << i));
              conf.set_cbit(pllout_select_portb_i_cb, pllout_select_portb[i]);
            }
          
          int pll_type_value = 0;
          if (inst->instance_of()->name() == "SB_PLL40_PAD")
            pll_type_value = 2;
          else if (inst->instance_of()->name() == "SB_PLL40_2_PAD")
            pll_type_value = 4;
          else if (inst->instance_of()->name() == "SB_PLL40_2F_PAD")
            pll_type_value = 6;
          else if (inst->instance_of()->name() == "SB_PLL40_CORE")
            pll_type_value = 3;
          else 
            {
              assert(inst->instance_of()->name() == "SB_PLL40_2F_CORE");
              pll_type_value = 7;
            }
          BitVector pll_type(3, pll_type_value);
          for (int i = 0; i < (int)pll_type.size(); ++i)
            {
              CBit pll_type_i_cb = chipdb->extra_cell_cbit(cell, fmt("PLLTYPE_" << i));
              conf.set_cbit(pll_type_i_cb, pll_type[i]);
            }
          
          BitVector shiftreg_div_mode = inst->get_param("SHIFTREG_DIV_MODE").as_bits();
          CBit shiftreg_div_mode_cb = chipdb->extra_cell_cbit(cell, "SHIFTREG_DIV_MODE");
          conf.set_cbit(shiftreg_div_mode_cb, shiftreg_div_mode[0]);
          
          Port *a = inst->find_port("PLLOUTGLOBAL");
          if (!a)
            a = inst->find_port("PLLOUTGLOBALA");
          assert(a);
          if (a->connected())
            {
              const auto &p2 = chipdb->cell_mfvs.at(cell).at("PLLOUT_A");
              Location glb_loc(p2.first, std::stoi(p2.second));
              int glb = chipdb->loc_pin_glb_num.at(glb_loc);
              
              const auto &ecb = chipdb->extra_bits.at(fmt("padin_glb_netwk." << glb));
              conf.set_extra_cbit(ecb);
            }
          
          Port *b = inst->find_port("PLLOUTGLOBALB");
          if (b && b->connected())
            {
              const auto &p2 = chipdb->cell_mfvs.at(cell).at("PLLOUT_B");
              Location glb_loc(p2.first, std::stoi(p2.second));
              int glb = chipdb->loc_pin_glb_num.at(glb_loc);
              
              const auto &ecb = chipdb->extra_bits.at(fmt("padin_glb_netwk." << glb));
              conf.set_extra_cbit(ecb);
            }
        }
      
      placement[inst] = cell;
    }
  
  // set IoCtrl configuration bits
  {
    const auto &func_cbits = chipdb->tile_nonrouting_cbits.at(TileType::IO);
    const CBit &lvds = func_cbits.at("IoCtrl.LVDS")[0];
    
    std::map<Location, int> loc_pll;
    int pll_idx = cell_type_idx(CellType::PLL);
    for (int cell : chipdb->cell_type_cells[pll_idx])
      {
        const auto &p2a = chipdb->cell_mfvs.at(cell).at("PLLOUT_A");
        Location a_loc(p2a.first, std::stoi(p2a.second));
        extend(loc_pll, a_loc, cell);
        
        const auto &p2b = chipdb->cell_mfvs.at(cell).at("PLLOUT_B");
        Location b_loc(p2b.first, std::stoi(p2b.second));
        extend(loc_pll, b_loc, cell);
      }
    
    for (const auto &p : package.pin_loc)
      {
        // unused io
        bool enable_input = false;
        bool pullup = true;  // default pullup
        
        const Location &loc = p.second;
        int pll_cell = lookup_or_default(loc_pll, loc, 0);
        if (pll_cell)
          {
            // FIXME only enable if inputs present
            enable_input = true;
            pullup = false;
          }
        else
          {
            int cell = chipdb->loc_cell(loc);
            int g = cell_gate[cell];
            if (g)
              {
                Instance *inst = gates[g];
                
                if (inst->find_port("D_IN_0")->connected()
                    || inst->find_port("D_IN_1")->connected()
                    || (models.is_gb_io(inst)
                        && inst->find_port("GLOBAL_BUFFER_OUTPUT")->connected()))
                  enable_input = true;
                pullup = inst->get_param("PULLUP").get_bit(0);
                conf.set_cbit(CBit(loc.tile(),
                                   lvds.row,
                                   lvds.col),
                              inst->get_param("IO_STANDARD").as_string() == "SB_LVDS_INPUT");
              }
          }
        
        const Location &ieren_loc = chipdb->ieren.at(loc);
        configure_io(ieren_loc, enable_input, pullup);
      }
    
    std::set<Location> ieren_image;
    for (const auto &p : chipdb->ieren)
      extend(ieren_image, p.second);
    for (int t = 0; t < chipdb->n_tiles; ++t)
      {
        if (chipdb->tile_type[t] != TileType::IO)
          continue;
        for (int p = 0; p <= 1; ++p)
          {
            bool enable_input = false;
            bool pullup = true;  // default pullup
            
            Location loc(t, p);
            if (contains(ieren_image, loc))
              continue;
            
            configure_io(loc, enable_input, pullup);
          }
      }
  }
  
  // set RamConfig.PowerUp configuration bit
  {
    const CBit &powerup = (chipdb->tile_nonrouting_cbits.at(TileType::RAMB)
                           .at("RamConfig.PowerUp")
                           [0]);
    for (int t : ramt_tiles)
      {
        Location loc(t,
                     0);
        int cell = chipdb->loc_cell(loc);
        int g = cell_gate[cell];
        assert(!g || models.is_ramX(gates[g]));
        conf.set_cbit(CBit(chipdb->ramt_ramb_tile(loc.tile()), // PowerUp on ramb tile
                           powerup.row,
                           powerup.col),
                      // active low
                      (chipdb->device == "1k"
                       ? !g
                       : (bool)g));
      }
  }
}

void
Placer::place()
{
  place_initial();
  // check();
  
  *logs << "annealing\n";
  *logs << "  initial wire length = " << wire_length() << "\n";
  
  int n_no_progress = 0;
  double avg_wire_length = wire_length();
  
  for (int iter=1;; iter++)
    {
      n_move = n_accept = 0;
      improved = false;

      if (iter % 50 == 0)
        *logs << "  at iteration #" << iter << ": temp = " << temp << ", wire length = " << wire_length() << "\n";
      
      for (int m = 0; m < 15; ++m)
        {
          for (int g : free_gates)
            {
              int new_cell = gate_random_cell(g);             
              int new_gate = cell_gate[new_cell];
              if (new_gate && chained[new_gate])
                continue;
              
              assert(!move_failed);
              move_gate(g, new_cell);
              accept_or_restore();
              
              // check();
            }
          
          for (unsigned c = 0; c < chains.chains.size(); ++c)
            {
              int gate0 = gate_idx.at(chains.chains[c][0]);
              if( locked[gate0] )
                  continue;

              std::pair<Location, bool> new_loc = chain_random_loc(c);
              if (!new_loc.second)
                  continue;

              assert(!move_failed);
              move_chain(c, new_loc.first);
              accept_or_restore();
              
              // check();
            }
        }
      
      if (improved)
        {
          n_no_progress = 0;
          // std::cout << "improved\n";
        }
      else
        ++n_no_progress;
      
      if (temp <= 1e-3
          && n_no_progress >= 5)
        break;
      
      double Raccept = (double)n_accept / (double)n_move;
#if 0
      std::cout << "Raccept " << Raccept
                << ", diameter = " << diameter
                << ", temp " << temp << "\n";
#endif
           int M = std::max(chipdb->width,
                       chipdb->height);

      double upper = 0.6,
        lower = 0.4;
      
      if (wire_length() < 0.95 * avg_wire_length)
        avg_wire_length = 0.8*avg_wire_length + 0.2*wire_length();
      else
        {
          if (Raccept >= 0.8)
            {
              temp *= 0.7;
            }
          else if (Raccept > upper)
            {
              if (diameter < M)
                ++diameter;
              else
                temp *= 0.9;
            }
          else if (Raccept > lower)
            {
              temp *= 0.95;
            }
          else
            {
              // Raccept < 0.3
              if (diameter > 1)
                --diameter;
              else
                temp *= 0.8;
            }
        } 
    }
  
  *logs << "  final wire length = " << wire_length() << "\n";
  
  configure();
  
#if 0
  int max_demand = 0;
  for (int t = 0; t < chipdb->n_tiles; ++t)
    {
      if (chipdb->tile_type[t] != TileType::LOGIC)
        continue;
      
      std::set<std::pair<Net *, int>> demand;
      for (int q = 0; q < 8; q ++)
        {
          Location loc(t, q);
          int cell = chipdb->loc_cell(loc);
          int g = cell_gate[cell];
          if (g)
            {
              Instance *inst = gates[g];
              
              for (int i = 0; i < 4; ++i)
                {
                  Net *n = inst->find_port(fmt("I" << i))->connection();
                  if (n
                      && !n->is_constant())
                    {
                      int parity = (q + i) & 1;
                      demand.insert(std::make_pair(n, parity));
                    }
                }
              
              Net *clk = inst->find_port("CLK")->connection();
              if (clk
                  && !clk->is_constant())
                {
                  int n = net_idx.at(clk);
                  if (!net_global[n])
                    demand.insert(std::make_pair(clk, 0));
                }

              Net *cen = inst->find_port("CEN")->connection();
              if (cen
                  && !cen->is_constant())
                {
                  int n = net_idx.at(cen);
                  if (!net_global[n])
                    demand.insert(std::make_pair(cen, 0));
                }
              
              Net *sr = inst->find_port("SR")->connection();
              if (sr
                  && !sr->is_constant())
                {
                  int n = net_idx.at(sr);
                  if (!net_global[n])
                    demand.insert(std::make_pair(sr, 0));
                }
            }
        }
      *logs << t 
            << " " << chipdb->tile_x(t)
            << " " << chipdb->tile_y(t)
            << " " << demand.size() << "\n";
      if ((int)demand.size() > max_demand)
        max_demand = demand.size();
    }
  *logs << "max_demand " << max_demand << "\n";
#endif
      
#if 0
  {
    int t = chipdb->tile(17, 16);
    for (const auto &p : placement)
      {
        int cell = p.second;
        const Location &loc = chipdb->cell_location[cell];
        if (loc.tile() == t)
          {
            Instance *inst = p.first;
            *logs << "LC " << inst << " " << loc.pos() << "\n";
            *logs << "  I0 " << inst->find_port("I0")->connection()->name() << "\n";
            *logs << "  I1 " << inst->find_port("I1")->connection()->name() << "\n";
            *logs << "  I2 " << inst->find_port("I2")->connection()->name() << "\n";
            *logs << "  I3 " << inst->find_port("I3")->connection()->name() << "\n";
            if (inst->find_port("CIN")->connected())
              *logs << "  CIN " << inst->find_port("CIN")->connection()->name() << "\n";
            if (inst->find_port("CLK")->connected())
              *logs << "  CLK " << inst->find_port("CLK")->connection()->name() << "\n";
            if (inst->find_port("SR")->connected())
              *logs << "  SR " << inst->find_port("SR")->connection()->name() << "\n";
            if (inst->find_port("CEN")->connected())
              *logs << "  CEN " << inst->find_port("CEN")->connection()->name() << "\n";
          }
      }
  }
#endif
  
  int n_pio = 0,
    n_plb = 0,
    n_bram = 0;
  std::set<int> seen;
  for (int i = 1; i <= n_gates; ++i)
    {
      int cell = gate_cell[i];
      int t = chipdb->cell_location[cell].tile();
      seen.insert(t);
    }
  for (int t : seen)
    {
      if (chipdb->tile_type[t] == TileType::LOGIC)
        ++n_plb;
      else if (chipdb->tile_type[t] == TileType::IO)
        ++n_pio;
      else if (chipdb->tile_type[t] == TileType::RAMT)
        ++n_bram;
    }
  
  *logs << "\nAfter placement:\n"
        << "PIOs       " << n_pio << " / " << package.pin_loc.size() << "\n"
        << "PLBs       " << n_plb << " / " << logic_tiles.size() << "\n"
        << "BRAMs      " << n_bram << " / " << ramt_tiles.size() << "\n"
        << "\n";
}

void
place(random_generator &rg, DesignState &ds)
{
  Placer placer(rg, ds);
  
  clock_t start = clock();
  placer.place();
  clock_t end = clock();
  
  *logs << "  place time "
        << std::fixed << std::setprecision(2)
        << (double)(end - start) / (double)CLOCKS_PER_SEC << "s\n";
}
