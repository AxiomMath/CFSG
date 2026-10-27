module

public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4Descent
public import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4Field

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSU)
open Matrix

namespace WitnessU4

variable {p f : ℕ} {K : Type} [Field K]

theorem primeFormConjHom_scalar (h : UnitaryFieldData p f K) {m : ℕ}
    (C : Matrix (Fin m) (Fin m) K) {d : Kˣ}
    (hd : GeneralLinearGroup.scalar (Fin m) d ∈ primeFormUnitary h C) :
    primeFormConjHom h C ⟨_, hd⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change GeneralLinearGroup.scalar (Fin m) d * (g : GL (Fin m) K) *
    (GeneralLinearGroup.scalar (Fin m) d)⁻¹ = g
  rw [← (commute_scalar d (g : GL (Fin m) K)).eq, mul_inv_cancel_right]

theorem unitaryNorm_pow (h : UnitaryFieldData p f K) (x : K) (k : ℕ) :
    h.norm (x ^ k) = h.norm x ^ k := by
  simp only [UnitaryFieldData.norm, map_pow, mul_pow]

theorem isInnerAut_primeFormConjHom (h : UnitaryFieldData 2 f K)
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    IsInnerAut (primeFormConjHom h _ A) := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hf := h.one_le
  set δ : Kˣ := GeneralLinearGroup.det (A : GL (Fin 4) K) with hδ
  have hδK : (δ : K) = ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det := rfl
  have hNδ : h.norm (δ : K) = 1 := by
    rw [hδK]
    exact norm_det_eq_one h 1 A.2
  set l : Kˣ := δ⁻¹ ^ (4 ^ (f - 1)) with hl
  have hl4 : l ^ 4 = δ⁻¹ := by
    refine Units.ext ?_
    have hcard : (4 : ℕ) ^ (f - 1) * 4 = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, h.card, pow_mul, ← pow_succ]
      congr 1
      omega
    rw [hl, ← pow_mul, Units.val_pow_eq_pow_val, hcard, FiniteField.pow_card]
  have hNl : h.norm (l : K) = 1 := by
    rw [hl, Units.val_pow_eq_pow_val, unitaryNorm_pow, Units.val_inv_eq_inv_val, norm_inv_eq, hNδ,
      inv_one, one_pow]
  have hlU : GeneralLinearGroup.scalar (Fin 4) l ∈
      primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hNl,
      one_smul]
  set s : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := ⟨_, hlU⟩ * A
    with hs
  have hsdet : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [hs, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← hδK, ← Units.val_pow_eq_pow_val, hl4, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ δ.ne_zero]
  have hsSU : (s : GL (Fin 4) K) ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    ⟨s.2, hsdet⟩
  have key : primeFormConjHom h _ A = primeFormConjHom h _ s := by
    rw [hs, map_mul, primeFormConjHom_scalar, one_mul]
  refine ⟨((⟨_, hsSU⟩ : gramSU h _) : primeFormP h _), ?_⟩
  rw [key]
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem glAut_eq_map {n : ℕ} (σ : K ≃+* K) (A : GL (Fin n) K) :
    glAut σ A = GeneralLinearGroup.map (σ : K →+* K) A :=
  Units.ext rfl

theorem exists_eq_conj_primeFormFieldHom (h : UnitaryFieldData 2 f K)
    (hC : IsPrimeFormGram (1 : GL (Fin 4) K))
    (α : MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
    (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ (φ : K ≃+* K) (H : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)),
      φ ^ 3 = 1 ∧ α = primeFormConjHom h _ H * primeFormFieldHom h hC φ *
        (primeFormConjHom h _ H)⁻¹ := by
  have := h.finite
  have hn : 3 ≤ 4 := by norm_num
  have hq : ¬(4 = 3 ∧ 2 ^ f = 2) := fun h' => absurd h'.1 (by norm_num)
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h hC hn hq α
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hout
    rw [hA, map_one, mul_one]
    exact isInnerAut_primeFormConjHom h A
  set x : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ⋊[primeFormFieldU h hC]
    (K ≃+* K) := ⟨A, φ⟩ with hx
  have hΨ : primeFormPsi h hC (x * (x * x)) = 1 := by
    rw [← pow_three, map_pow, hx, primeFormPsi_apply, ← hA, hα]
  obtain ⟨hright, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hΨ
  have hφ3 : φ ^ 3 = 1 := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right] at hright
    rw [pow_three]
    exact hright
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hc' : GeneralLinearGroup.scalar (Fin 4) c = (A : GL (Fin 4) K) *
      GeneralLinearGroup.map (φ : K →+* K) (A : GL (Fin 4) K) *
      GeneralLinearGroup.map ((φ * φ : K ≃+* K) : K →+* K) (A : GL (Fin 4) K) := by
    rw [← hc, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [hx, Subgroup.coe_mul, coe_primeFormFieldU, map_mul, glAut_eq_map, mul_assoc]
    rfl
  obtain ⟨H₀, d, hH⟩ := exists_unitary_mul_map_eq_scalar_mul (h := h) (n := 4) (by norm_num) hσ
    A hc'
  set H : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := ⟨H₀.1, H₀.2⟩
    with hHdef
  refine ⟨φ, H, hφ3, ?_⟩
  have hdmem : GeneralLinearGroup.scalar (Fin 4) d ∈
      primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have h1 : GeneralLinearGroup.scalar (Fin 4) d =
        (A : GL (Fin 4) K) * glAut φ (H : GL (Fin 4) K) * (H : GL (Fin 4) K)⁻¹ := by
      rw [hHdef]
      exact (eq_mul_inv_of_mul_eq hH.symm)
    rw [h1]
    exact mul_mem (mul_mem A.2 (glAut_mem_primeFormUnitary h hC φ H.2)) (inv_mem H.2)
  have hAeq : A = ⟨_, hdmem⟩ * H * (primeFormFieldU h hC φ H)⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq hH)
  rw [hA, hAeq, map_mul, map_mul, map_inv, primeFormConjHom_scalar, one_mul,
    ← primeFormField_conj_eq h hC φ H]
  group

end WitnessU4

open WitnessU4 in
theorem inputs47Core_witnessU4 :
    ∀ n : ℕ, 1 ≤ n → ∀ α : MulAut (projSU 4 2 n), α ^ 3 = 1 → ¬ IsInnerAut α →
      HasLocalWitness α := by
  intro n hn α hα hout
  have hU := unitaryFieldData_galoisField 2 n hn
  have hC : IsPrimeFormGram (1 : GL (Fin 4) (GaloisField 2 (2 * n))) := isPrimeFormGram_one_GL
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (by norm_num)
    (fun h' => absurd h'.1 (by norm_num))
  let e : projSU 4 2 n ≃* primeFormP hU
      ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) : Matrix (Fin 4) (Fin 4) _) :=
    (projSUEquivStatedProj 4 2 n).trans ((unitaryPSUEquiv hU (by norm_num)).symm.trans e₃.symm)
  rw [← hasLocalWitness_congr_iff e]
  have hβ : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hβout : ¬ IsInnerAut (MulAut.congr e α) := fun h' => hout ((isInnerAut_congr e α).mp h')
  obtain ⟨φ, H, hφ3, hβeq⟩ := exists_eq_conj_primeFormFieldHom hU hC _ hβ hβout
  rw [hβeq]
  exact (hasLocalWitness_primeFormFieldHom hU hC hφ3).conj (primeFormConjHom hU _ H)

end CFSG.RankThree.PartTwo.Sec4
