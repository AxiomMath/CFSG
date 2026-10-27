module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchBlock


public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.LieType.RootSystem CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.PhanCode

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)

theorem cartan_sl_of_coxeter
    (h : ∀ i j, i ≠ j → coxeterMatrix hA i j = 2 ∨ coxeterMatrix hA i j = 3) :
    ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1 := by
  intro i j hij
  have hM : coxeterMatrix hA i j = TauCeti.coxeterOrder (A i j * A j i) :=
    TauCeti.coxeterMatrixOfCartanMatrix_apply A hA.apply_self
      (fun _ _ h => hA.apply_mul_apply_mem_of_ne h) i j
  have hmem := hA.apply_mul_apply_mem_of_ne hij
  rcases h i j hij with h2 | h3
  · left
    have h2' : TauCeti.coxeterOrder (A i j * A j i) = 2 := by rw [← hM]; exact h2
    rcases (TauCeti.coxeterOrder_eq_two_iff hmem).mp h2' with h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact h0
    · exact hA.apply_eq_zero_symm h0
  · right
    have hprod : A i j * A j i = 1 := by
      have h3' : TauCeti.coxeterOrder (A i j * A j i) = 3 := by rw [← hM]; exact h3
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h0 | h1 | h2 | h3''
      · rw [h0] at h3'; simp at h3'
      · exact h1
      · rw [h2] at h3'; simp at h3'
      · rw [h3''] at h3'; simp at h3'
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h1 | h1
    · have := hA.apply_le_zero_of_ne hij; omega
    · exact h1

theorem coxeter_eq_two_of_cartan_eq_zero {i j : Fin n} (hij : i ≠ j) (h : A i j = 0) :
    coxeterMatrix hA i j = 2 := by
  exact (TauCeti.coxeterMatrixOfCartanMatrix_apply_eq_two_iff A hA.apply_self
    (fun _ _ h => hA.apply_mul_apply_mem_of_ne h)
    (fun _ _ h => hA.apply_eq_zero_symm h) hij).mpr h

theorem path_cartan_of_match {c : PhanCode} (hc : c.IsFlagCode) (σ : Fin c.rank → Fin n)
    (hdiag : ∀ i, A (σ i) (σ i) = 2)
    (hadj : ∀ i j : Fin c.rank, i ≠ j → A (σ i) (σ j) = if c.coxN i j = 3 then -1 else 0)
    (k l : Fin c.rank) :
    A (σ k) (σ l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0 := by
  cases c <;> simp only [IsFlagCode] at hc
  all_goals
    first
    | exact hc.elim
    | (by_cases hkl : k = l
       · subst hkl
         simp [hdiag]
       · rw [if_neg hkl, hadj k l hkl]
         fin_cases k <;> fin_cases l <;> simp_all [PhanCode.coxN, PhanCode.rank])

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
