module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Pt2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Base

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F45Ru
open scoped Pointwise

theorem two_of_pairs {X : Type*} [Group X] {V : Type*} [MulAction X V] {a w₀ w₁ : V}
    (N : Set V) (hpairs : ∀ u ∈ N, ∀ u' ∈ N, u ≠ u' →
      ∃ h : X, h • a = a ∧ h • w₀ = u ∧ h • w₁ = u') :
    ∀ b ∈ N, ∀ c ∈ N, ∀ b' ∈ N, ∀ c' ∈ N, b ≠ c → b' ≠ c' →
      ∃ g : X, g • a = a ∧ g • b = b' ∧ g • c = c' := by
  intro b hb c hc b' hb' c' hc' hbc hbc'
  obtain ⟨h₁, h₁a, h₁b, h₁c⟩ := hpairs b hb c hc hbc
  obtain ⟨h₂, h₂a, h₂b, h₂c⟩ := hpairs b' hb' c' hc' hbc'
  refine ⟨h₂ * h₁⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 h₁a.symm, h₂a]
  · rw [mul_smul, inv_smul_eq_iff.2 h₁b.symm, h₂b]
  · rw [mul_smul, inv_smul_eq_iff.2 h₁c.symm, h₂c]

theorem nbr_inl_zero {b : Vtx}
    (hb : incGraph.Adj (Sum.inl 0) b) : ∃ k : Fin 27, b = Sum.inr k ∧ k.val < 3 := by
  rcases b with q | k
  · exact absurd hb (not_adj_inl_inl 0 q)
  · refine ⟨k, rfl, ?_⟩
    have hk : k.val ∈ (List.range 27).filter (fun k => (lnTab.getD k []).contains 0) :=
      List.mem_filter.2 ⟨List.mem_range.2 k.2, List.contains_iff_mem.2 hb⟩
    rw [p_spec.2.2.1, (chkF45Pt_unpack).1] at hk
    simp at hk
    omega

theorem two_pairs_pt :
    ∀ i < 3, ∀ j < 3, i ≠ j → ∃ h : Y, h • (Sum.inl 0 : Vtx) = Sum.inl 0 ∧
      h • (Sum.inr (0 : Fin 27) : Vtx) = Sum.inr (lnOf i) ∧
      h • (Sum.inr (1 : Fin 27) : Vtx) = Sum.inr (lnOf j) := by
  intro i hi j hj hij
  have hp : ∀ i < 3, ∀ j < 3, i ≠ j → ∃ t < 6, pairs3.getD t (0, 0) = (i, j) := by decide
  have hL : ∀ i < 3, ([0, 1, 2] : List ℕ).getD i 0 = i := by decide
  obtain ⟨t, ht, htp⟩ := hp i hi j hj hij
  obtain ⟨hap, hs1, hs2⟩ := (chkF45Pt_unpack).2.2.2.2.2 t ht
  rw [htp, (chkF45Pt_unpack).1] at hs1 hs2
  simp only [hL i hi, hL j hj] at hs1 hs2
  refine ⟨repY (two1.getD t []), ?_, ?_, ?_⟩
  · rw [smul_inl_zero_iff, mem_P1_iff]
    apply Fin.ext
    show (((wordP (two1.getD t [])) 0 : Fin 45) : ℕ) = 0
    rw [applyW_eq]
    exact hap
  · refine congrArg Sum.inr (lnImg_repY (a := 0) (b := lnOf i) ?_)
    rw [lnOf_val (by omega)]
    exact hs1
  · refine congrArg Sum.inr (lnImg_repY (a := 1) (b := lnOf j) ?_)
    rw [lnOf_val (by omega)]
    exact hs2

theorem two_pt :
    ∀ b c b' c' : Vtx, incGraph.Adj (Sum.inl 0) b → incGraph.Adj (Sum.inl 0) c → b ≠ c →
      incGraph.Adj (Sum.inl 0) b' → incGraph.Adj (Sum.inl 0) c' → b' ≠ c' →
      ∃ g : Y, g • (Sum.inl 0 : Vtx) = Sum.inl 0 ∧ g • b = b' ∧ g • c = c' := by
  intro b c b' c' hb hc hbc hb' hc' hbc'
  refine two_of_pairs (a := (Sum.inl 0 : Vtx)) (w₀ := Sum.inr 0) (w₁ := Sum.inr 1)
    (incGraph.neighborSet (Sum.inl 0)) ?_ b hb c hc b' hb' c' hc' hbc hbc'
  intro u hu u' hu' hne
  obtain ⟨k, rfl, hk⟩ := nbr_inl_zero hu
  obtain ⟨k', rfl, hk'⟩ := nbr_inl_zero hu'
  have hne' : k.val ≠ k'.val := fun h => hne (congrArg Sum.inr (Fin.ext h))
  obtain ⟨h, h1, h2, h3⟩ := two_pairs_pt k.val hk k'.val hk' hne'
  refine ⟨h, h1, ?_, ?_⟩
  · rw [h2]
    exact congrArg Sum.inr (Fin.ext (lnOf_val k.2))
  · rw [h3]
    exact congrArg Sum.inr (Fin.ext (lnOf_val k'.2))

theorem modelBase_pt :
    ModelBase incGraph 4 (Sum.inl 0) (pCoreOf 2 (MulAction.stabilizer Y (Sum.inl 0 : Vtx))) := by
  have hS : IsSylowTwoOf T (MulAction.stabilizer Y (Sum.inl 0 : Vtx)) := by
    rw [stabilizer_inl_zero]
    exact CFSG.Quasithin.F7.isSylowTwoOf_mono_right isSylow_T (T_le_B0.trans B0_le_P1) le_top
  refine modelBase_of_core hS repsP1 repsP1_mem repsP1_dec (b₀ := Sum.inl (ptOf b01)) hfar_pt
    hfree_pt ?_ ?_ two_pt
  · rw [card_nbrs_inl]
  · rw [card_nbrs_inl]
    decide

end CFSG.Quasithin.H13.F431.U42
