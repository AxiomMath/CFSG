module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Ln
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Pt3

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F45Ru
open scoped Pointwise

theorem nbr_inr_zero {b : Vtx}
    (hb : incGraph.Adj (Sum.inr 0) b) : ∃ p : Fin 45, b = Sum.inl p ∧ p.val ∈ L0 := by
  rcases b with p | k
  · refine ⟨p, rfl, ?_⟩
    have h : p ∈ lnF 0 := adj_inr_inl.1 hb
    rw [lnF_zero] at h
    exact h
  · exact absurd hb (not_adj_inr_inr 0 k)

theorem L0_getD_lt : ∀ i < 5, L0.getD i 0 < 45 := by decide

theorem L0_index : ∀ p : Fin 45, p.val ∈ L0 → ∃ i < 5, L0.getD i 0 = p.val := by decide

theorem two_pairs_ln :
    ∀ i < 5, ∀ j < 5, i ≠ j → ∃ h : Y, h • (Sum.inr 0 : Vtx) = Sum.inr 0 ∧
      h • (Sum.inl (ptOf (L0.getD 0 0)) : Vtx) = Sum.inl (ptOf (L0.getD i 0)) ∧
      h • (Sum.inl (ptOf (L0.getD 1 0)) : Vtx) = Sum.inl (ptOf (L0.getD j 0)) := by
  intro i hi j hj hij
  have hp : ∀ i < 5, ∀ j < 5, i ≠ j → ∃ t < 20, pairs5.getD t (0, 0) = (i, j) := by decide
  obtain ⟨t, ht, htp⟩ := hp i hi j hj hij
  obtain ⟨hs, h1, h2⟩ := (chkF45Ln_unpack).2.2.2.2 t ht
  simp only [htp] at h1 h2
  refine ⟨repY (two2.getD t []), ?_, ?_, ?_⟩
  · rw [smul_inr_zero_iff]
    exact repY_mem_P2 hs
  · rw [Sum.smul_inl]
    refine congrArg Sum.inl (Fin.ext ?_)
    rw [smul_point]
    show ((wordP (two2.getD t [])) (ptOf (L0.getD 0 0)) : ℕ) = (ptOf (L0.getD i 0)).val
    rw [← (repL_wordP _).2, ptOf_val (L0_getD_lt 0 (by norm_num)), ptOf_val (L0_getD_lt i hi)]
    exact h1
  · rw [Sum.smul_inl]
    refine congrArg Sum.inl (Fin.ext ?_)
    rw [smul_point]
    show ((wordP (two2.getD t [])) (ptOf (L0.getD 1 0)) : ℕ) = (ptOf (L0.getD j 0)).val
    rw [← (repL_wordP _).2, ptOf_val (L0_getD_lt 1 (by norm_num)), ptOf_val (L0_getD_lt j hj)]
    exact h2

theorem two_ln :
    ∀ b c b' c' : Vtx, incGraph.Adj (Sum.inr 0) b → incGraph.Adj (Sum.inr 0) c → b ≠ c →
      incGraph.Adj (Sum.inr 0) b' → incGraph.Adj (Sum.inr 0) c' → b' ≠ c' →
      ∃ g : Y, g • (Sum.inr 0 : Vtx) = Sum.inr 0 ∧ g • b = b' ∧ g • c = c' := by
  intro b c b' c' hb hc hbc hb' hc' hbc'
  refine two_of_pairs (a := (Sum.inr 0 : Vtx)) (w₀ := Sum.inl (ptOf (L0.getD 0 0)))
    (w₁ := Sum.inl (ptOf (L0.getD 1 0))) (incGraph.neighborSet (Sum.inr 0)) ?_ b hb c hc b' hb' c'
    hc' hbc hbc'
  intro u hu u' hu' hne
  obtain ⟨p, rfl, hp⟩ := nbr_inr_zero hu
  obtain ⟨p', rfl, hp'⟩ := nbr_inr_zero hu'
  obtain ⟨i, hi, hip⟩ := L0_index p hp
  obtain ⟨j, hj, hjp⟩ := L0_index p' hp'
  have hij : i ≠ j := by
    rintro rfl
    exact hne (congrArg Sum.inl (Fin.ext (hip.symm.trans hjp)))
  obtain ⟨h, h1, h2, h3⟩ := two_pairs_ln i hi j hj hij
  refine ⟨h, h1, ?_, ?_⟩
  · rw [h2]
    exact congrArg Sum.inl (Fin.ext (by rw [ptOf_val (L0_getD_lt i hi), hip]))
  · rw [h3]
    exact congrArg Sum.inl (Fin.ext (by rw [ptOf_val (L0_getD_lt j hj), hjp]))

theorem modelBase_ln :
    ModelBase incGraph 4 (Sum.inr 0) (pCoreOf 2 (MulAction.stabilizer Y (Sum.inr 0 : Vtx))) := by
  have hS : IsSylowTwoOf T (MulAction.stabilizer Y (Sum.inr 0 : Vtx)) := by
    rw [stabilizer_inr_zero]
    exact CFSG.Quasithin.F7.isSylowTwoOf_mono_right isSylow_T (T_le_B0.trans B0_le_P2) le_top
  refine modelBase_of_core hS repsP2 repsP2_mem repsP2_dec (b₀ := Sum.inr (lnOf b02)) hfar_ln
    hfree_ln ?_ ?_ two_ln
  · rw [card_nbrs_inr]
    decide
  · rw [card_nbrs_inr]
    decide

end CFSG.Quasithin.H13.F431.U42
