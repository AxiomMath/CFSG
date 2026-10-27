module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree

public section

namespace CFSG.StandardType

namespace RecipeFieldSpU

section Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem conjAut_mul_fieldAut_conj_of_pow_orderOf [Finite K] (hr : 1 ≤ r) (A : gsp r K)
    (σ : K ≃+* K) (hα : (conjAut r K A * fieldAut r K σ) ^ orderOf σ = 1) :
    ∃ H : gsp r K,
      conjAut r K A * fieldAut r K σ = conjAut r K H * fieldAut r K σ * (conjAut r K H)⁻¹ := by
  rw [conjAut_mul_fieldAut_pow, pow_orderOf_eq_one, map_one, mul_one] at hα
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.KFacts.exists_scalar_of_conjAut_eq_one hr hα
  have hc' : twNorm σ ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      (orderOf σ) = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [← coe_gspNorm, hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      smul_one_eq_diagonal]
  obtain ⟨H, d, hH⟩ := exists_gsp_mul_map_eq_smul hr rfl A hc'
  refine ⟨H, ?_⟩
  have hAeq : A = ⟨_, CFSG.RankThree.PartTwo.KFacts.scalar_mem_gsp d⟩ * H * (gspFieldMap σ H)⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq hH)
  rw [hAeq, map_mul, map_mul, map_inv, CFSG.RankThree.PartTwo.KFacts.conjAut_scalar_eq_one,
    one_mul, ← fieldAut_mul_conjAut_mul_inv σ H]
  group

end Symplectic

section Unitary

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag InndiagSU

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ} [NeZero d]

theorem primeForm_conj_of_pow_orderOf_eq_one (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ p ^ f = 2))
    (A : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) (σ : K ≃+* K)
    (hodd : Odd (orderOf σ))
    (hα : (primeFormConjHom h _ A *
      primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ) ^ orderOf σ = 1) :
    ∃ H : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
      primeFormConjHom h _ A * primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ =
        primeFormConjHom h _ H * primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ *
          (primeFormConjHom h _ H)⁻¹ := by
  have hC1 := isPrimeFormGram_one (K := K) (n := d)
  obtain ⟨-, -, hker, -, -, -, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC1 hd hq
  rw [conjHom_mul_fieldHom_pow, ← primeFormPsi_apply] at hα
  obtain ⟨-, c, -, hleft⟩ := (hker _).mp hα
  have hc : twNorm σ ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (orderOf σ) =
      (c : K) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [← coe_uNorm h hC1]
    rw [hleft, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, smul_one_eq_diagonal]
  obtain ⟨H, e, hH⟩ := exists_unitary_mul_map_eq_smul rfl hodd A hc
  refine ⟨H, ?_⟩
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

end Unitary

end RecipeFieldSpU

end CFSG.StandardType

end
