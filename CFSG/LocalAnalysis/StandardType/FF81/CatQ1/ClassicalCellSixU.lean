module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalCubeData
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalFrameU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

private lemma cq1_scalar_eq_smul_one {n : ℕ} {F : Type*} [Field F] (a : F) :
    Matrix.scalar (Fin n) a = a • (1 : Matrix (Fin n) (Fin n) F) := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem exists_su_order_nine_commute {ℓ f n : ℕ} {F : Type*} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 6 ≤ n) {B : Matrix (Fin n) (Fin n) F}
    (hB : (B.map h.bar)ᵀ * B = 1) {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ X : SpecialLinearGroup (Fin n) F,
      (((X : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ * X = 1) ∧
      (X : Matrix (Fin n) (Fin n) F) * B = B * X ∧ X ^ 9 = 1 ∧
      ∀ a : F, ((X ^ 3 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ a • 1 := by
  obtain ⟨P₁, P₂, S, hF, hP₁, hP₂⟩ := exists_isOrthogonalFrame_of_unitary_nonCube h hn hB hB3 hc
  have hcσ : h.bar c * c = 1 :=
    bar_mul_self_eq_one_of_pow_three_eq_smul h.bar (by omega) hB hB3
  obtain ⟨lam, ω, j, hω, hω1, hlam, hlamσ, hωσ⟩ :=
    @exists_cubeData_of_unitary_nonCube F _ h.finite h.bar c hcσ hc
  let R : Matrix (Fin n) (Fin n) F := orthRotation B P₁ P₂ lam ω j
  have hdet : R.det = 1 := hF.orthRotation_det hB3 hlam hω
  let X : SpecialLinearGroup (Fin n) F := ⟨R, hdet⟩
  refine ⟨X, ?_, ?_, ?_, ?_⟩
  · change ((R.map h.bar)ᵀ * R = 1)
    exact hF.orthRotation_unitary h.bar hP₁ hP₂ hB hlamσ hωσ
  · change (R * B = B * R)
    exact hF.orthRotation_commute
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    change R ^ 9 = 1
    exact hF.orthRotation_pow_nine hB3 hlam hω
  · intro a
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change R ^ 3 ≠ a • 1
    exact hF.orthRotation_pow_three_ne hB3 hlam hω hω1 a

private lemma cq1_exists_pow_three_scalar_of_mem_normOneScalars {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (C : Matrix (Fin n) (Fin n) F)
    {X : SpecialLinearGroup (Fin n) F} (g : gramSU h C)
    (hg : (g : GL (Fin n) F) = SpecialLinearGroup.toGL X)
    (hmem : g ^ 3 ∈ normOneScalars h (gramSU h C) n) :
    ∃ a : F, ((X ^ 3 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = a • 1 := by
  obtain ⟨cc, -, -, hscal⟩ := (mem_normOneScalars).mp hmem
  have hg3eq : (SpecialLinearGroup.toGL X) ^ 3 = GeneralLinearGroup.scalar (Fin n) cc := by
    have hh := hscal
    rw [Subgroup.coe_pow] at hh
    rwa [hg] at hh
  have hg3' : SpecialLinearGroup.toGL (X ^ 3) = GeneralLinearGroup.scalar (Fin n) cc := by
    rw [map_pow]
    exact hg3eq
  refine ⟨(cc : F), ?_⟩
  have hh := congrArg (fun u : GL (Fin n) F =>
    ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hg3'
  rwa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar,
    cq1_scalar_eq_smul_one] at hh

private lemma cq1_orderOf_mk_eq_nine {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (C : Matrix (Fin n) (Fin n) F)
    {X : SpecialLinearGroup (Fin n) F} (hX9 : X ^ 9 = 1)
    (hX3 : ∀ a : F, ((X ^ 3 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ a • 1)
    (g : gramSU h C) (hg : (g : GL (Fin n) F) = SpecialLinearGroup.toGL X) :
    orderOf (g : primeFormP h C) = 9 := by
  have hg9 : g ^ 9 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hg, ← map_pow, hX9, map_one]
  have hx9 : (g : primeFormP h C) ^ 9 = 1 := by
    rw [← QuotientGroup.mk_pow, hg9, QuotientGroup.mk_one]
  have hx3 : (g : primeFormP h C) ^ 3 ≠ 1 := by
    intro h3
    have h3' : ((g ^ 3 : gramSU h C) : primeFormP h C) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact h3
    have hmem : g ^ 3 ∈ normOneScalars h (gramSU h C) n :=
      (QuotientGroup.eq_one_iff (g ^ 3)).mp h3'
    obtain ⟨a, ha⟩ := cq1_exists_pow_three_scalar_of_mem_normOneScalars h C g hg hmem
    exact hX3 a ha
  have hord := orderOf_eq_prime_pow (p := 3) (n := 1) hx3 hx9
  norm_num at hord
  exact hord

private lemma cq1_mk_fixed_of_commute {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (C : Matrix (Fin n) (Fin n) F)
    (A : primeFormUnitary h C) (g : gramSU h C)
    (hcomm : (A : GL (Fin n) F) * (g : GL (Fin n) F) = (g : GL (Fin n) F) * (A : GL (Fin n) F)) :
    primeFormConjHom h C A (g : primeFormP h C) = (g : primeFormP h C) := by
  have hAg : (⟨A * g * (A : GL (Fin n) F)⁻¹, conj_mem_gramSU h C A.2 g.2⟩ :
      gramSU h C) = g := by
    apply Subtype.ext
    change (A : GL (Fin n) F) * (g : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹ =
      (g : GL (Fin n) F)
    rw [hcomm, mul_inv_cancel_right]
  rw [primeFormConjHom_mk, hAg]

theorem exists_order_nine_fixed_of_unitary_nonCube {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 6 ≤ n)
    {A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)} {c : F}
    (hA3 : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 =
      c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ x : primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), orderOf x = 9 ∧
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A x = x := by
  have hB : (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ *
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    have h1 := (mem_primeFormUnitary (h := h)
      (C := ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (g := (A : GL (Fin n) F))).mp A.2
    simpa using h1
  obtain ⟨X, hXu, hXc, hX9, hX3⟩ := exists_su_order_nine_commute h hn hB hA3 hc
  have hgmem : SpecialLinearGroup.toGL X ∈
      gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [mem_gramSU]
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      simpa only [Units.val_one, Matrix.mul_one] using hXu
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact X.2
  let g : gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    ⟨SpecialLinearGroup.toGL X, hgmem⟩
  let x : primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    (g : primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
  have hcomm : (A : GL (Fin n) F) * (g : GL (Fin n) F) =
      (g : GL (Fin n) F) * (A : GL (Fin n) F) := by
    apply Units.ext
    simp only [Units.val_mul]
    exact hXc.symm
  refine ⟨x, ?_, ?_⟩
  · exact cq1_orderOf_mk_eq_nine h _ hX9 hX3 g rfl
  · exact cq1_mk_fixed_of_commute h _ A g hcomm

end CFSG.StandardType.FF81.CatQ1
