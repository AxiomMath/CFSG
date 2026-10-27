module

public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3Four

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

theorem exists_mulEquiv_primeFormP_of_U3 {D : Type} [Group D] {m : ℕ}
    (hD : StatedClassicalModel D .PSU 3 2 m) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 m K),
      Nonempty (D ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  have h : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  exact ⟨K, inferInstance, h, ⟨eD.trans ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.trans
    (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3))⟩⟩

theorem exists_odd_dvd_orderOf_mul_inv_U3 {D : Type} [Group D] {m : ℕ} (hm : 2 ≤ m)
    (hD : StatedClassicalModel D .PSU 3 2 m) (α : MulAut D) (hα : orderOf α = 2)
    (hout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ (x : D) (n : ℕ), Odd n ∧ ¬ n ∣ 105 ∧ n ∣ orderOf (α x * x⁻¹) := by
  obtain ⟨K, _, _, h, ζ, hζ⟩ :=
    CFSG.LocalAnalysis.even_unitary_three_outer_involution_bar_conjugate hm hD α hα hout
  have hφ : ∀ c, (fieldDataHermitianForm h).conj c = h.bar c := fun c => rfl
  have key : ∃ (x₀ : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (n : ℕ),
      Odd n ∧ ¬ n ∣ 105 ∧ n ∣ orderOf (primeFormFieldAut h isPrimeFormGram_one
        (fieldDataHermitianForm h).conj x₀ * x₀⁻¹) := by
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨x₀, hx₀⟩ := thirteen_dvd_orderOf_fieldAut_mul_inv h isPrimeFormGram_one _ hφ
      exact ⟨x₀, 13, by decide, by decide, hx₀⟩
    · obtain ⟨x₀, hx₀⟩ := dvd_orderOf_fieldAut_mul_inv_diag h isPrimeFormGram_one _ hφ
      refine ⟨x₀, 2 ^ m + 1, (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one, fun hd => ?_, hx₀⟩
      have hle := Nat.le_of_dvd (by norm_num) hd
      have hm7 : m ≤ 6 := by
        by_contra hm7
        have : 2 ^ 7 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases m <;> norm_num at hd
  obtain ⟨x₀, n, hn, hn105, hdvd⟩ := key
  refine ⟨ζ x₀, n, hn, hn105, ?_⟩
  rw [hζ, ← map_inv, ← map_mul, MulEquiv.orderOf_eq]
  exact hdvd

theorem congr_mem_range_conj_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (β : MulAut G) :
    MulAut.congr e β ∈ (MulAut.conj : H →* MulAut H).range ↔
      β ∈ (MulAut.conj : G →* MulAut G).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, MulEquiv.ext fun g => e.injective ?_⟩
    have h1 := congrArg (fun γ : MulAut H => γ (e g)) hy
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.symm_apply_apply] at h1
    simp [MulAut.conj_apply, h1]
  · rintro ⟨y, rfl⟩
    refine ⟨e y, MulEquiv.ext fun g => ?_⟩
    simp [MulAut.conj_apply, MulAut.congr_apply]

theorem exists_hom_ringEquiv_of_U3 {D : Type} [Group D] {m : ℕ} (hm : 2 ≤ m)
    (hD : StatedClassicalModel D .PSU 3 2 m) :
    ∃ (K : Type) (_ : Field K) (Φ : MulAut D →* (K ≃+* K)) (σ₀ : K ≃+* K),
      (∀ β : MulAut D, β * β = 1 → Φ β = 1 → β ∈ (MulAut.conj : D →* MulAut D).range) ∧
      ∀ σ : K ≃+* K, σ * σ = 1 → σ = 1 ∨ σ = σ₀ := by
  obtain ⟨K, _, h, ⟨ε⟩⟩ := exists_mulEquiv_primeFormP_of_U3 hD
  have hq : ¬(3 = 3 ∧ 2 ^ m = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  refine ⟨K, inferInstance, (primeFormFieldFactor h hC (by norm_num) hq).comp
    (MulAut.congr ε).toMonoidHom, (fieldDataHermitianForm h).conj, fun β hβ hΦ => ?_,
    fun σ hσ => ?_⟩
  · rw [← congr_mem_range_conj_iff ε]
    set β' := MulAut.congr ε β with hβ'
    by_cases h1 : β' = 1
    · rw [h1]
      exact ⟨1, map_one _⟩
    have hβ'2 : β' * β' = 1 := by rw [hβ', ← map_mul, hβ, map_one]
    have hord : orderOf β' = 2 := orderOf_eq_prime (by rw [sq]; exact hβ'2) h1
    have hD' : β' ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← ker_primeFormFieldFactor h hC (by norm_num) hq, MonoidHom.mem_ker]
      exact hΦ
    exact (even_unitary_involution_matrix_lifts h hC (by norm_num) hq β' hord).2.2.2 β' hD' hord
  · rcases ringEquiv_eq_refl_or_bar h hσ with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (RingEquiv.ext fun c => (h1 c).trans rfl)

end CFSG.RankThree.PartTwo.Sec20
