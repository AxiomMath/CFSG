module

public import CFSG.RankThree.PartOne.U5K.Hyp.Transport

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge

variable {f : ℕ} {K : Type} [Field K]

theorem two_mem_inn (h : UnitaryFieldData 2 f K)
    {α : MulAut (primeFormP h (idGram K 5))} (hα : α ∈ primeFormD h (idGram K 5)) {k : ℕ}
    (hk : α ^ (2 ^ k) = 1) :
    α ∈ (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range := by
  have hfin := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  set ιR := hypToPrimeForm h hR with hιR
  set θ : MulAut (primeFormP h (idGram K 5)) ≃* MulAut (hypPSU h 2 1) :=
    MulAut.congr ιR.symm with hθ
  obtain ⟨X, rfl⟩ := hα
  have hθX : θ (primeFormConjHom h (idGram K 5) X) =
      linearSimAut h (by norm_num : 1 ≤ 2) le_rfl (toSimilitude h hR X) :=
    mulAut_congr_conj_eq h hR X
  have hDlin : θ (primeFormConjHom h (idGram K 5) X) ∈ Hyp.Dlin h := by
    rw [hθX]
    exact ⟨_, Hyp.mem_Gam1.2 rfl, rfl⟩
  have hk' : (θ (primeFormConjHom h (idGram K 5) X)) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hk, map_one]
  obtain ⟨z, hz⟩ := Hyp.Dlin_two_mem_Pi hDlin hk'
  refine ⟨ιR z, ?_⟩
  apply θ.injective
  rw [← hz]
  have := mulAut_congr_conj ιR.symm (ιR z)
  exact this.trans (by rw [MulEquiv.symm_apply_apply])

theorem exists_perm_zero_one {i j : Fin 5} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = i ∧ σ 1 = j := by
  set σ₁ : Equiv.Perm (Fin 5) := Equiv.swap 0 i with hσ₁
  set j₁ : Fin 5 := σ₁.symm j with hj₁
  have hσj : σ₁ j₁ = j := by rw [hj₁]; exact σ₁.apply_symm_apply j
  have hj₀ : j₁ ≠ 0 := by
    intro h0
    apply hij
    rw [h0] at hσj
    rw [← hσj, hσ₁, Equiv.swap_apply_left]
  refine ⟨σ₁ * Equiv.swap 1 j₁, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hj₀), hσ₁,
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hσj]

@[expose] def stdIdx : HypIndex 2 1 ≃ Fin 5 where
  toFun x := match x with
    | .inl a => ![0, 2] a
    | .inr (.inl _) => 4
    | .inr (.inr a) => ![1, 3] a
  invFun t := ![Sum.inl 0, Sum.inr (Sum.inr 0), Sum.inl 1, Sum.inr (Sum.inr 1),
    Sum.inr (Sum.inl 0)] t
  left_inv x := by
    rcases x with a | k | a
    · fin_cases a <;> rfl
    · fin_cases k; rfl
    · fin_cases a <;> rfl
  right_inv t := by fin_cases t <;> rfl

end CFSG.RankThree.PartOne.U5K.Kf
