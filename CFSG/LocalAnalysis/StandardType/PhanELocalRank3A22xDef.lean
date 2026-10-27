module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCls
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def jShift (v : Fin 4 → K) : Fin 4 → K :=
  ![0, 0, sg K f (v 0), sg K f (v 1)]

@[expose] noncomputable def D22x : ClsData K where
  ok _ := True
  good c M := c.comap rho ≠ Vsub 4 2 ⊔ Submodule.span K (jShift f '' (M : Set (Fin 4 → K)))

private theorem plh_mem_farSet_a3_22x_iff (x : FlagK K 4) :
    x ∈ farSet 4 [0, 2, 4] ↔ x.E 2 ⊓ Vsub (K := K) 4 2 = ⊥ := by
  have hd : ∀ i, i < ([0, 2, 4] : List ℕ).length →
      ([0, 2, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  rw [mem_farSet_iff (K := K) (n := 4) (d := [0, 2, 4]) hd]
  constructor
  · intro h
    have h' := (h 1 (by decide) 2 (by decide)).1 (by decide)
    simpa using h'
  · intro h
    intro i hi j hj
    have hi3 : i < 3 := by simpa using hi
    interval_cases i
    · constructor
      · intro _
        rw [show ([0, 2, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq]
      · intro hge
        have hj4 : j = 4 := by
          have : 4 ≤ j := by simpa using hge
          omega
        subst hj4
        rw [show ([0, 2, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, sup_bot_eq]
        exact x.top 4 le_rfl
    · constructor
      · intro hjc
        have hj2 : j ≤ 2 := by
          have : j + 2 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 2) (x.mono hj2)).trans
          (le_of_eq h))
      · intro hge
        have hj2 : 2 ≤ j := by
          have : 4 ≤ j + 2 := by simpa using hge
          omega
        have hsup : x.E 2 ⊔ Vsub (K := K) 4 2 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 2)
            (Vsub (K := K) 4 2)
          rw [h, finrank_bot, add_zero, FlagK.finrank_E_two,
            finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)] at hsum
          omega
        have hle : x.E 2 ⊔ Vsub (K := K) 4 2 ≤ x.E j ⊔ Vsub (K := K) 4 2 :=
          sup_le_sup (x.mono hj2) le_rfl
        rw [hsup] at hle
        exact top_le_iff.mp hle
    · constructor
      · intro hjc
        have hj0 : j = 0 := by
          have : j + 4 ≤ 4 := by simpa using hjc
          omega
        subst hj0
        rw [FlagK.E_zero, bot_inf_eq]
      · intro _
        rw [show ([0, 2, 4] : List ℕ).getD 2 0 = 4 from rfl, Vsub_self, sup_top_eq]

private theorem plh_blockU_a3_22x_block1 (x : FlagK K 4) :
    blockU K 4 [0, 2, 4] x.E 1 1 = x.E 1 ⊔ Vsub (K := K) 4 2 := by
  have h4 : ([0, 2, 4] : List ℕ).getD 2 0 = 4 := rfl
  have h2 : ([0, 2, 4] : List ℕ).getD 1 0 = 2 := rfl
  rw [blockU, h4, h2, Vsub_self, inf_top_eq]

private theorem plh_blockU_a3_22x_block0 (x : FlagK K 4) :
    blockU K 4 [0, 2, 4] x.E 0 1 = x.E 3 ⊓ Vsub (K := K) 4 2 := by
  have h2 : ([0, 2, 4] : List ℕ).getD 1 0 = 2 := rfl
  have h0 : ([0, 2, 4] : List ℕ).getD 0 0 = 0 := rfl
  rw [blockU, h2, h0, Vsub_zero, sup_bot_eq]

theorem genSet_a3_22x_eq :
    set22x K f = admSet (AdmS (D22x (K := K) f)) := by
  ext x
  simp only [set22x, Set.mem_setOf_eq, admSet, AdmS, D22x, true_and]
  rw [plh_mem_farSet_a3_22x_iff (K := K) x,
    plh_blockU_a3_22x_block1 (K := K) x,
    plh_blockU_a3_22x_block0 (K := K) x,
    Submodule.comap_map_eq (rho (K := K)) (x.E 1), ker_rho (K := K)]
  exact Iff.rfl

end CFSG.ClassicalInvolution.Phan.PhanE

end
