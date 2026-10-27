module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofFormDescent
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofLinBasics

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open Matrix

section GraphConj

variable {K : Type} [Field K]

theorem ringZpow_apply_eq_self {ρ : K ≃+* K} {x : K} (hx : ρ x = x) (m : ℤ) : (ρ ^ m) x = x := by
  have hn : ∀ n : ℕ, (ρ ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      change (ρ ^ n) (ρ x) = x
      rw [hx, ih]
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, hn]
  · rw [_root_.zpow_neg, zpow_natCast]
    conv_lhs => rw [← hn n]
    exact (ρ ^ n).symm_apply_apply x

@[expose] def fixSub (ρ : K ≃+* K) : Subfield K :=
  RingHom.eqLocusField (ρ : K →+* K) (RingHom.id K)

theorem mem_fixSub {ρ : K ≃+* K} {x : K} : x ∈ fixSub ρ ↔ ρ x = x :=
  Iff.rfl

theorem exists_graph_conj [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {A : GL (Fin 3) K} {σ ρ : K ≃+* K}
    (hcomm : conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K * fieldAut 3 K ρ =
      fieldAut 3 K ρ * (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K))
    {m : ℤ} (hsq : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) ^ 2 = fieldAut 3 K ρ ^ m) :
    ∃ k : GL (Fin 3) K, GeneralLinearGroup.map (ρ : K →+* K) k = k ∧
      conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K =
        conjAut 3 K k * (fieldAut 3 K σ * dualAut 3 K) * (conjAut 3 K k)⁻¹ := by
  classical
  have hρσ : fieldAut 3 K σ * fieldAut 3 K ρ = fieldAut 3 K ρ * fieldAut 3 K σ := by
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm]
  have h1 : conjAut 3 K A = conjAut 3 K (GeneralLinearGroup.map (ρ : K →+* K) A) := by
    have e1 : conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K * fieldAut 3 K ρ =
        conjAut 3 K A * (fieldAut 3 K ρ * fieldAut 3 K σ * dualAut 3 K) := by
      rw [mul_assoc (conjAut 3 K A * fieldAut 3 K σ), dualAut_mul_fieldAut, ← mul_assoc,
        mul_assoc (conjAut 3 K A), hρσ]
      group
    have e2 : fieldAut 3 K ρ * (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) =
        conjAut 3 K (GeneralLinearGroup.map (ρ : K →+* K) A) *
          (fieldAut 3 K ρ * fieldAut 3 K σ * dualAut 3 K) := by
      rw [← mul_assoc, ← mul_assoc, fieldAut_mul_conjAut]
      group
    rw [e1, e2] at hcomm
    exact mul_right_cancel hcomm
  obtain ⟨ν, hν⟩ := exists_scalar_of_conjAut_eq h1.symm
  have h2 : conjAut 3 K (A * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose A)) * fieldAut 3 K (σ * σ) * dualAut 3 K ^ 0 =
      conjAut 3 K 1 * fieldAut 3 K (ρ ^ m) * dualAut 3 K ^ 0 := by
    rw [pow_zero, mul_one, mul_one, map_one, one_mul, map_zpow, ← hsq,
      sq_conjAut_fieldAut_dualAut]
  obtain ⟨hσρ, -⟩ :=
    ProjectivePlane.standard_form_unique (le_refl 3) (Nat.zero_le 1) (Nat.zero_le 1) h2
  have h3 : conjAut 3 K (A * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose A)) = conjAut 3 K 1 := by
    have e := h2
    rw [pow_zero, mul_one, mul_one, hσρ] at e
    exact mul_right_cancel e
  obtain ⟨μ, hμ⟩ := exists_scalar_of_conjAut_eq h3
  rw [mul_one] at hμ
  obtain ⟨M, hM⟩ : ∃ M, M = (A : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  obtain ⟨Mi, hMi⟩ : ∃ Mi, Mi = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMdet : M.det ≠ 0 := by rw [hM]; exact (Matrix.isUnits_det_units A).ne_zero
  have hρM : ∀ a b, ρ (M a b) = ν * M a b := by
    intro a b
    have e := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) a b) hν
    simp only [Units.val_mul, coe_scalar_three, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul] at e
    rw [hM]
    exact e
  have hσM : ∀ a b, M a b = μ * σ (M b a) := by
    have e := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) hμ
    simp only [Units.val_mul, coe_scalar_three] at e
    have hmapσ : ∀ X : GL (Fin 3) K, ((GeneralLinearGroup.map (σ : K →+* K) X : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (X : Matrix (Fin 3) (Fin 3) K).map σ := fun _ => rfl
    rw [hmapσ, GeneralLinearGroup.coe_inverseTranspose, ← hMi, ← hM] at e
    have e2 : M = (μ : K) • (Mᵀ).map σ := by
      have hid : (Miᵀ).map σ * (Mᵀ).map σ = 1 := by
        change (Miᵀ).map (σ : K →+* K) * (Mᵀ).map (σ : K →+* K) = 1
        rw [← Matrix.map_mul, ← transpose_mul, hMMi, transpose_one]
        simp
      calc M = M * ((Miᵀ).map σ * (Mᵀ).map σ) := by rw [hid, Matrix.mul_one]
        _ = (μ : K) • (Mᵀ).map σ := by
          rw [← Matrix.mul_assoc, e, Matrix.smul_mul, Matrix.one_mul]
    intro a b
    conv_lhs => rw [e2]
    rfl
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra h
    push Not at h
    apply hMdet
    have : M = 0 := by ext a b; exact h a b
    simp [this]
  have hnorm : ∀ i : ℕ, ∀ a b, (ρ ^ i) (M a b) =
      (∏ j ∈ Finset.range i, (ρ ^ j) (ν : K)) * M a b := by
    intro i
    induction i with
    | zero => intro a b; simp
    | succ i ih =>
      intro a b
      rw [pow_succ, Finset.prod_range_succ]
      change (ρ ^ i) (ρ (M a b)) = _
      rw [hρM, map_mul, ih]
      ring
  have : Finite (K ≃+* K) := CFSG.GH74.GLS.IVK.instFiniteRingEquiv K
  set r := orderOf ρ with hr
  have hprod : ∏ j ∈ Finset.range r, (ρ ^ j) (ν : K) = 1 := by
    have e := hnorm r a₀ b₀
    rw [hr, pow_orderOf_eq_one] at e
    have e' : (1 - ∏ j ∈ Finset.range (orderOf ρ), (ρ ^ j) (ν : K)) * M a₀ b₀ = 0 := by
      change M a₀ b₀ = _ at e
      linear_combination e
    exact (sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hab)).symm
  obtain ⟨y, hy0, hy⟩ :=
    CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField ρ hr.symm hprod
  set M' : Matrix (Fin 3) (Fin 3) K := y • M with hM'
  have hM'L : ∀ a b, M' a b ∈ fixSub ρ := fun a b => by
    rw [mem_fixSub, hM', Matrix.smul_apply, smul_eq_mul, map_mul, hρM]
    linear_combination (M a b) * hy
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy0
  have hM'σ : ∀ a b, M' a b = (y * μ / σ y) * σ (M' b a) := fun a b => by
    rw [hM', Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hσM a b]
    field_simp
  have hM'det : M'.det ≠ 0 := by
    rw [hM', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hy0) hMdet
  have hσL : ∀ x, σ x ∈ fixSub ρ ↔ x ∈ fixSub ρ := by
    intro x
    rw [mem_fixSub, mem_fixSub]
    have e : ρ (σ x) = σ (ρ x) := by
      have := CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K ρ σ
      exact congrArg (fun φ : K ≃+* K => φ x) this
    rw [e]
    exact σ.injective.eq_iff
  have hσσ : ∀ x ∈ fixSub ρ, σ (σ x) = x := by
    intro x hx
    have e : σ (σ x) = (σ * σ) x := rfl
    rw [e, hσρ]
    exact ringZpow_apply_eq_self (mem_fixSub.mp hx) m
  obtain ⟨k, c, hkL, hc0, hkc⟩ :=
    exists_mul_map_transpose_eq hp2 (fixSub ρ) σ hσL hσσ M' hM'L hM'det hM'σ
  refine ⟨k, ?_, ?_⟩
  · apply Units.ext
    ext a b
    exact mem_fixSub.mp (hkL a b)
  ·
    have hcy : c * y ≠ 0 := mul_ne_zero hc0 hy0
    have hk : k * GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose k⁻¹) =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (c * y) hcy) * A := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_scalar_three]
      change (k : Matrix (Fin 3) (Fin 3) K) *
        (((GeneralLinearGroup.inverseTranspose k⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)).map σ = _
      rw [GeneralLinearGroup.coe_inverseTranspose, inv_inv, transpose_map, hkc, hM', ← hM,
        smul_smul, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
    have e : conjAut 3 K k * (fieldAut 3 K σ * dualAut 3 K) * (conjAut 3 K k)⁻¹ =
        conjAut 3 K (k * GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose k⁻¹)) * fieldAut 3 K σ * dualAut 3 K := by
      rw [← map_inv, map_mul, mul_assoc (conjAut 3 K k) (fieldAut 3 K σ * dualAut 3 K),
        mul_assoc (fieldAut 3 K σ), dualAut_mul_conjAut, ← mul_assoc (fieldAut 3 K σ),
        fieldAut_mul_conjAut]
      group
    rw [e, hk, map_mul, conjAut_scalar, one_mul]

end GraphConj

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
