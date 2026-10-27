module

public import CFSG.Quasithin.H13.AS91Sec7Defs
public import CFSG.Quasithin.H13.AS91Sec8Base
public import CFSG.Quasithin.H13.AS91Sec8Glue
public import CFSG.Quasithin.H13.AS91Sec8Sim
public import CFSG.Quasithin.H13.AS91Sec8Native
public import CFSG.Quasithin.Vol2.Ch8InputsB
public import CFSG.Quasithin.H13.AS91Sec5Tri
public import CFSG.Quasithin.H13.AS91Sec8Kaut
public import CFSG.Quasithin.H13.AS91Sec8Kchar
public import CFSG.Quasithin.H13.AS91Sec8EquivK

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94 CFSG.Blueprint

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem inf_stab_eq' {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hLU : c.G1 ⊓ stabilizer G y ≤ c.G2) :
    stabilizer G c.x0 ⊓ stabilizer G y =
      c.K ⊔ c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y := by
  rw [c.stab_x0]
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hk, s, hs, rfl⟩ := c.G2_eq_mul (hLU hg)
    have hkM : k ∈ c.G1 ⊓ stabilizer G y :=
      Subgroup.mem_inf.mpr ⟨c.K_le_G1 hk, c.K_le_stab hy hk⟩
    have hsM : s ∈ c.G1 ⊓ stabilizer G y := by
      have := mul_mem (inv_mem hkM) hg
      simpa using this
    refine mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ?_)
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨c.CZ_le_G3 hs, (Subgroup.mem_inf.mp hsM).1⟩,
      (Subgroup.mem_inf.mp hsM).2⟩
  · refine sup_le (le_inf c.K_le_G1 (c.K_le_stab hy)) ?_
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem isEquivalence' (hKchar : Stmt8_Kchar) (hKaut : Stmt8_Kaut)
    (hJ : HypJ4 G z) (hloc : CosetGeomLocal c.G1 c.G2 c.G3) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) (hLU : c.G1 ⊓ stabilizer G y ≤ c.G2) {Gb : Type*} [Group Gb]
    {Xb : Type*} [MulAction Gb Xb] {Ib : Subgroup Gb} {xb yb : Xb}
    {β : ↥(stabilizer G c.x0) ≃* ↥(stabilizer Gb xb)} {ζ : ↥c.G3 ≃* ↥Ib}
    (hs : IsSimilarity c.G3 c.x0 y Ib xb yb β ζ) :
    IsEquivalence c.G3 c.x0 y Ib xb yb β ζ := by
  obtain ⟨t, htS, htx, hty, u, hu, hux, huy, htu⟩ := c.exists_swap_fix hy hyx
  obtain ⟨h₁, hh₁, hh₁x, hh₁y⟩ := hloc.twoTrans c.x0 y c.x0 u c.x0_mem_ptsL hy
    c.x0_mem_ptsL hu hyx.symm hux.symm
  exact equivalence_of_charK hs c.K
    (le_inf (c.K_le_stab c.x0_mem_ptsL) (c.K_le_stab hy)) (hKaut G z hJ c)
    (hKchar G z hJ c y hy hyx) ⟨t, c.CZ_le_G3 htS⟩ ⟨h₁, (Subgroup.mem_inf.mp hh₁).2⟩ u htx hty htu
    hh₁x hh₁y (c.mem_normalizer_K (c.CZ_le_G2 htS))
    (c.mem_normalizer_K (Subgroup.mem_inf.mp hh₁).1) (c.inf_stab_eq' hy hLU)

end Loc49

theorem inputAS91_core
    (h49 : Stmt4_9) (h52 : Stmt5_2u) (hlu : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (h55 : Stmt5_5)
    (h65 : Stmt6_5u) (h79 : Stmt7_9) (h823 : Stmt8_2_3) (h83 : Stmt8_3) (h84 : Stmt8_4) :
    CFSG.Quasithin.H13.InputAS91 := by
  have h531 : Stmt5_3_1u := stmt5_3_1u_of_gamma2 hG2
  intro G _ _ hsimple hnonab z hz hcore haut hnwc
  have hJ : HypJ4 G z := ⟨hsimple, hnonab, hz, hcore, haut, hnwc⟩
  obtain ⟨c⟩ := h49 G z hJ
  obtain ⟨z', hJ'⟩ := exists_hypJ4_native
  obtain ⟨c'⟩ := h49 NativeSporadic.J4 z' hJ'
  have hloc := c.coset_geom_local' h52 h65 hJ
  have hloc' := c'.coset_geom_local' h52 h65 hJ'
  obtain ⟨y, hy, hyx⟩ := hloc.exists_pt
  obtain ⟨y', hy', hyx'⟩ := hloc'.exists_pt
  have hU := hloc.isUniquenessSystem hy hyx
  have hU' := hloc'.isUniquenessSystem hy' hyx'
  obtain ⟨ζ₀, hζ₀x, hζ₀e⟩ := h83 G z hJ c NativeSporadic.J4 z' hJ' c' y y' hy hyx hy' hyx'
  obtain ⟨a, haI, hay⟩ := h84 G z hJ c NativeSporadic.J4 z' hJ' c' y y' hy hyx hy' hyx'
  obtain ⟨β, ζ, hsim⟩ := as92Thm4 G (G ⧸ c.G1) NativeSporadic.J4 (NativeSporadic.J4 ⧸ c'.G1)
    c.Delta c.G3 _ c.x0 y c'.Delta c'.G3 _ c'.x0 y' hU hU'
    (h823 G z hJ c y hy hyx) (h823 NativeSporadic.J4 z' hJ' c' y' hy' hyx') a ζ₀ hay hζ₀x haI hζ₀e
  have heq := c.isEquivalence' (stmt8_Kchar_of hlu) stmt8_Kaut hJ hloc hy hyx
    (hlu G z hJ c y hy hyx) hsim
  obtain ⟨t', ht', ht'x, -⟩ := hloc'.swap hy' hyx'
  have hbase := isBase_orbitSubgraph_colGraph c'.G1 c'.G2 c'.G3 (CosetGeomLocal.adj hy' hyx')
    ⟨t', ht', ht'x⟩ (h79 NativeSporadic.J4 z' hJ' c') (h55 NativeSporadic.J4 z' hJ' c')
    (c'.rank_hyp h531 hJ' hloc' hy' hyx')
  obtain ⟨φ, -, -⟩ := recognition hU hU' heq hbase hJ'.simple
  exact ⟨φ⟩

theorem inputAS91_of_2c
    (h49 : Stmt4_9) (h52 : Stmt5_2u) (h2c : Stmt5_2c) (h55 : Stmt5_5)
    (h65 : Stmt6_5u) (h79 : Stmt7_9) (h823 : Stmt8_2_3) (h83 : Stmt8_3) (h84 : Stmt8_4) :
    CFSG.Quasithin.H13.InputAS91 :=
  inputAS91_core h49 h52 (stmt5_lineU_of_2c h2c) (stmt5_gamma2_of_2c h2c) h55 h65 h79 h823 h83
    h84

theorem inputAS91_of_312
    (h49 : Stmt4_9) (h52 : Stmt5_2u) (h2c : Stmt5_2c) (h312 : Stmt3_12)
    (h65 : Stmt6_5u) (h79 : Stmt7_9) (h823 : Stmt8_2_3) (h83 : Stmt8_3) (h84 : Stmt8_4) :
    CFSG.Quasithin.H13.InputAS91 :=
  inputAS91_of_2c h49 h52 h2c (stmt5_5_of h2c h312) h65 h79 h823 h83 h84

theorem inputAS91_of_312_max
    (h49 : Stmt4_9) (h12 : Stmt5_Max12) (h13 : Stmt5_Max13) (h2c : Stmt5_2c) (h312 : Stmt3_12)
    (h65 : Stmt6_5u) (h79 : Stmt7_9) (h823 : Stmt8_2_3) (h83 : Stmt8_3) (h84 : Stmt8_4) :
    CFSG.Quasithin.H13.InputAS91 :=
  inputAS91_of_312 h49 (stmt5_2u_of_max h12 h13) h2c h312 h65 h79 h823 h83 h84

end CFSG.Quasithin.H13.AS91
