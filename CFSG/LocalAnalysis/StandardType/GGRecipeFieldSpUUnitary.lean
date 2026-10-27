module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUHerm
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.StandardType

namespace RecipeFieldSpU

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag InndiagSU

section General

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}

section Powers

variable {C : GL (Fin d) K} (hC : IsPrimeFormGram C)

@[expose] noncomputable def uNorm (σ : K ≃+* K)
    (A : primeFormUnitary h (C : Matrix (Fin d) (Fin d) K)) :
    ℕ → primeFormUnitary h (C : Matrix (Fin d) (Fin d) K)
  | 0 => 1
  | j + 1 => A * primeFormFieldU h hC σ (uNorm σ A j)

theorem coe_uNorm (σ : K ≃+* K) (A : primeFormUnitary h (C : Matrix (Fin d) (Fin d) K)) (j : ℕ) :
    (((uNorm h hC σ A j : primeFormUnitary h _) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      twNorm σ ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [twNorm_succ, ← ih]
    rfl

theorem conjHom_mul_fieldHom_pow (σ : K ≃+* K)
    (A : primeFormUnitary h (C : Matrix (Fin d) (Fin d) K)) (j : ℕ) :
    (primeFormConjHom h _ A * primeFormFieldHom h hC σ) ^ j =
      primeFormConjHom h _ (uNorm h hC σ A j) * primeFormFieldHom h hC (σ ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, map_one, uNorm, map_one, one_mul]
  | succ j ih =>
    rw [pow_succ', ih, pow_succ']
    calc primeFormConjHom h _ A * primeFormFieldHom h hC σ *
          (primeFormConjHom h _ (uNorm h hC σ A j) * primeFormFieldHom h hC (σ ^ j)) =
        primeFormConjHom h _ A * (primeFormFieldHom h hC σ *
          primeFormConjHom h _ (uNorm h hC σ A j) * (primeFormFieldHom h hC σ)⁻¹) *
            (primeFormFieldHom h hC σ * primeFormFieldHom h hC (σ ^ j)) := by group
      _ = primeFormConjHom h _ (uNorm h hC σ A (j + 1)) *
            primeFormFieldHom h hC (σ * σ ^ j) := by
        rw [primeFormField_conj_eq, ← map_mul, ← map_mul]
        rfl

end Powers

variable [NeZero d]

theorem primeForm_conj_of_pow_eq_one (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ p ^ f = 2)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (A : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) (σ : K ≃+* K)
    (hσ1 : σ ≠ 1)
    (hα : (primeFormConjHom h _ A *
      primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ) ^ ℓ = 1) :
    orderOf σ = ℓ ∧ ∃ H : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
      primeFormConjHom h _ A * primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ =
        primeFormConjHom h _ H * primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ *
          (primeFormConjHom h _ H)⁻¹ := by
  have hC1 := isPrimeFormGram_one (K := K) (n := d)
  obtain ⟨-, -, hker, -, -, -, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC1 hd hq
  rw [conjHom_mul_fieldHom_pow, ← primeFormPsi_apply] at hα
  obtain ⟨hright, c, -, hleft⟩ := (hker _).mp hα
  have hσℓ : σ ^ ℓ = 1 := hright
  have hσo : orderOf σ = ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact orderOf_eq_prime hσℓ hσ1
  have hc : twNorm σ ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ℓ =
      (c : K) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [← coe_uNorm h hC1]
    rw [hleft, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, smul_one_eq_diagonal]
  obtain ⟨H, e, hH⟩ := exists_unitary_mul_map_eq_smul hσo (hℓ.odd_of_ne_two hℓ2) A hc
  refine ⟨hσo, H, ?_⟩
  have hemem : GeneralLinearGroup.scalar (Fin d) e ∈
      primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h1 : GeneralLinearGroup.scalar (Fin d) e =
        (A : GL (Fin d) K) * glAut σ (H : GL (Fin d) K) * (H : GL (Fin d) K)⁻¹ := by
      rw [hH, mul_inv_cancel_right]
    rw [h1]
    exact mul_mem (mul_mem A.2 (glAut_mem_primeFormUnitary h hC1 σ H.2)) (inv_mem H.2)
  have he1 : primeFormConjHom h _ ⟨_, hemem⟩ = 1 := by
    have h1 := (hker ⟨⟨_, hemem⟩, 1⟩).mpr ⟨rfl, e,
      norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 hemem, rfl⟩
    rwa [primeFormPsi_apply, map_one, mul_one] at h1
  have hAeq : A = ⟨_, hemem⟩ * H * (primeFormFieldU h hC1 σ H)⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq hH)
  rw [hAeq, map_mul, map_mul, map_inv, he1, one_mul, ← primeFormField_conj_eq h hC1 σ H]
  group


end General

section Recipe

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem congr_symm_field_mem (hd : 1 ≤ d) (σ : K ≃+* K) :
    (MulAut.congr (projEquiv h hd)).symm
        (primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ) ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  refine ⟨σ, fun g g' hgg' => ?_⟩
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (projEquiv h hd).symm (primeFormFieldAut h (isPrimeFormGram_one (K := K) (n := d)) σ
    (projEquiv h hd (g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) =
      (g' : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [projEquiv_mk, primeFormFieldAut_mk, projEquiv_symm_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change ((glAut σ (g : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
  rw [coe_glAut]
  exact hgg'.symm

theorem primeFormFieldHom_injective (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    Function.Injective (primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d))) := by
  obtain ⟨-, -, hker, -, -, -, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have h1 := (hker ⟨1, σ⟩).mp (by rw [primeFormPsi_apply, map_one, one_mul, hσ])
  exact h1.1

include h in
theorem ggRawFieldConj_unitary [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGRawFieldConj p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  intro _ _ u hu f hf huf hpow
  have hd1 : 1 ≤ d := by omega
  have : NeZero d := ⟨by omega⟩
  have hC1 := isPrimeFormGram_one (K := K) (n := d)
  set E := MulAut.congr (projEquiv h hd1) with hE
  obtain ⟨A, hA⟩ := congr_mem_primeFormD h hd1 hK hu
  have hF : Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) ≤
        (primeFormFieldHom h hC1).range.comap E.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨σ, hσ⟩ := RecipeFieldSU.congr_field_eq h hd1 hφ
    exact ⟨σ, hσ.symm⟩
  obtain ⟨σ, hσ⟩ := hF hf
  have hEf : E f = primeFormFieldHom h hC1 σ := hσ.symm
  have hEuf : E (u * f) = primeFormConjHom h _ A * primeFormFieldHom h hC1 σ := by
    rw [map_mul, ← hA, hEf]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply huf
    have h1 : u * f ∈ RecipeFieldSU.recIU d h hd1 := by
      rw [RecipeFieldSU.mem_recIU_iff, ← hE, hEuf, map_one, mul_one]
      exact ⟨A, rfl⟩
    rw [← RecipeFieldSU.coe_recIU h hK hd1]
    exact h1
  have hpow' : (primeFormConjHom h _ A * primeFormFieldHom h hC1 σ) ^ p = 1 := by
    rw [← hEuf, ← map_pow, hpow, map_one]
  obtain ⟨hσo, H, hH⟩ := primeForm_conj_of_pow_eq_one h hd hq hp hp2 A σ hσ1 hpow'
  refine ⟨E.symm (primeFormFieldHom h hC1 σ), congr_symm_field_mem h hd1 σ,
    E.symm (primeFormConjHom h _ H), congr_symm_mem h hd1 H, ?_, ?_⟩
  · have h1 := orderOf_injective E.symm.toMonoidHom E.symm.injective (primeFormFieldHom h hC1 σ)
    have h2 := orderOf_injective _ (primeFormFieldHom_injective h hd hq) σ
    rw [h2, hσo] at h1
    exact h1
  · apply E.injective
    rw [hEuf, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hH

end Recipe

end RecipeFieldSpU

open RecipeFieldSpU

theorem ggRawFieldConjOn_unitary : GGRawFieldConjOn fun _ => GGInndiagUnitaryLabel :=
  fun _ hp hp2 _ hlab hS => largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK =>
    ggRawFieldConj_unitary (unitaryFieldData_of_card hn hK) hK hd hq hp hp2

end CFSG.StandardType
