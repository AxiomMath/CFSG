module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.Proj

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem exists_ringEquiv_eq_sq : ∃ σ : K ≃+* K, ∀ x, σ x = x ^ 2 := by
  obtain ⟨σ, hσ, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (n := 2 * f)
      (by have := h.one_le; omega) h.card
  exact ⟨σ, hσ⟩

theorem exists_unit_pow_four_eq_det_norm_one {n : ℕ} (A : uU h n) :
    ∃ c : Kˣ, c ^ 4 = GeneralLinearGroup.det (A : GL (Fin n) K) ∧ h.norm (c : K) = 1 := by
  let M : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hA : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hdet : h.bar M.det * M.det = 1 := by
    have h1 := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    rw [show (M.map h.bar).det = h.bar M.det from (RingHom.map_det h.bar M).symm] at h1
    exact h1
  have hpow : M.det ^ (2 ^ f + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply, hdet]
  have hodd : Odd (2 ^ f + 1) :=
    (even_two (α := ℕ)).pow_of_ne_zero (by have := h.one_le; omega) |>.add_one
  have hcop : Nat.Coprime 4 (2 ^ f + 1) := by
    have h2 : Nat.Coprime 2 (2 ^ f + 1) := Nat.coprime_two_left.2 hodd
    simpa using h2.pow_left 2
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := M.det)
    (hcop.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow))
  have hc4 : (M.det ^ t) ^ 4 = M.det := by
    have h1 : (M.det ^ t) ^ 4 = M.det ^ (4 * t) := by rw [← pow_mul, mul_comm t 4]
    rw [h1, pow_mul, ht]
  have hc0 : M.det ^ t ≠ 0 := by
    intro h0
    refine GeneralLinearGroup.det_ne_zero (A : GL (Fin n) K) ?_
    rw [← hc4, h0, zero_pow (by norm_num : 4 ≠ 0)]
  refine ⟨Units.mk0 (M.det ^ t) hc0, ?_, ?_⟩
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc4]
    rfl
  · show ((Units.mk0 (M.det ^ t) hc0 : Kˣ) : K) *
      h.bar ((Units.mk0 (M.det ^ t) hc0 : Kˣ) : K) = 1
    rw [Units.val_mk0, map_pow, ← mul_pow, mul_comm M.det (h.bar M.det), hdet, one_pow]

theorem uConjAut_four_mem_range (A : uU h 4) :
    uConjAut h (by norm_num) A ∈
      (MulAut.conj : StatedProj (StatedSU 4 (2 ^ f) K) →* MulAut _).range := by
  obtain ⟨cU, hcU4, hnorm⟩ := exists_unit_pow_four_eq_det_norm_one h A
  have hCmem : GeneralLinearGroup.scalar (Fin 4) cU ∈ uU h 4 := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul,
      hnorm, one_smul]
  set C₀ : uU h 4 := ⟨GeneralLinearGroup.scalar (Fin 4) cU, hCmem⟩ with hC₀
  set A₀ : uU h 4 := C₀⁻¹ * A with hA₀
  have hdetC₀ : GeneralLinearGroup.det (C₀ : GL (Fin 4) K) = cU ^ 4 := by
    rw [hC₀]
    simp
  have hdetA₀ : GeneralLinearGroup.det (A₀ : GL (Fin 4) K) = 1 := by
    rw [hA₀, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hdetC₀, hcU4,
      inv_mul_cancel]
  have hA₀SU : (A₀ : GL (Fin 4) K) ∈ StatedSU 4 (2 ^ f) K := by
    rw [statedSU_eq_gramSU h, mem_gramSU_iff_unitary]
    exact ⟨A₀.2, by simpa using congrArg Units.val hdetA₀⟩
  have hC1 : uConjAut h (n := 4) (by norm_num) C₀ = 1 := by
    rw [hC₀]
    exact (uConjAut_eq_one_iff h (n := 4) (by norm_num) ⟨_, hCmem⟩).2 ⟨cU, rfl⟩
  have hsplit : uConjAut h (n := 4) (by norm_num) A =
      uConjAut h (n := 4) (by norm_num) A₀ := by
    have hmul : C₀ * A₀ = A := by rw [hA₀]; group
    calc uConjAut h (n := 4) (by norm_num) A
        = uConjAut h (n := 4) (by norm_num) (C₀ * A₀) := by rw [hmul]
      _ = uConjAut h (n := 4) (by norm_num) C₀ * uConjAut h (n := 4) (by norm_num) A₀ :=
          map_mul _ _ _
      _ = uConjAut h (n := 4) (by norm_num) A₀ := by rw [hC1, one_mul]
  have hinner : uConjAut h (n := 4) (by norm_num) A₀ =
      MulAut.conj (projH (StatedSU 4 (2 ^ f) K) ⟨(A₀ : GL (Fin 4) K), hA₀SU⟩) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := projH_surjective (H := StatedSU 4 (2 ^ f) K) x
    rw [MulAut.conj_apply, uConjAut_proj h (by norm_num) A₀ g, ← map_mul, ← map_inv,
      ← map_mul]
    exact congrArg _ (Subtype.ext rfl)
  exact ⟨projH (StatedSU 4 (2 ^ f) K) ⟨(A₀ : GL (Fin 4) K), hA₀SU⟩, by rw [hsplit, hinner]⟩

theorem exists_conj_mul_uFieldAut_pow {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2)
    (α : MulAut (StatedProj (StatedSU 4 (2 ^ f) K))) :
    ∃ y : StatedProj (StatedSU 4 (2 ^ f) K), ∃ j : ℕ,
      α = MulAut.conj y * uFieldAut h (by norm_num) σ ^ j := by
  obtain ⟨σ', hσ', -, htop', hcard', -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (n := 2 * f)
      (by have := h.one_le; omega) h.card
  have := Nat.finite_of_card_ne_zero (by rw [hcard']; have := h.one_le; omega)
  have hσσ' : σ = σ' := RingEquiv.ext fun x => (hσ x).trans (hσ' x).symm
  have htop : Subgroup.zpowers σ = ⊤ := by rw [hσσ', htop']
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h (n := 4) (by norm_num) (by norm_num) α
  obtain ⟨y, hy⟩ := uConjAut_four_mem_range h A
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff φ σ).mp
    (mem_powers_iff_mem_zpowers.mpr (htop ▸ Subgroup.mem_top φ))
  exact ⟨y, j, by rw [hα, hy, ← map_pow, hj]⟩

theorem uFieldAut_pow_two_mul_eq_one {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) :
    uFieldAut h (n := 4) (by norm_num) σ ^ (2 * f) = 1 := by
  have := h.finite
  have := Fintype.ofFinite K
  have hiter : ∀ j : ℕ, ∀ x : K, (σ ^ j) x = x ^ 2 ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        rw [pow_succ']
        change σ ((σ ^ j) x) = x ^ 2 ^ (j + 1)
        rw [ih x, hσ, ← pow_mul, ← pow_succ]
  have hσ1 : σ ^ (2 * f) = 1 := by
    refine RingEquiv.ext fun x => ?_
    rw [hiter, ← h.card, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rfl
  rw [← map_pow, hσ1, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
