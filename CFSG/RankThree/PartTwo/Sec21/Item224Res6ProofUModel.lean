module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofTv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem card_sq_of_unitary (h : UnitaryFieldData 2 f K) : Nat.card K = (2 ^ f) ^ 2 := by
  rw [h.card, ← pow_mul, mul_comm]

@[expose] noncomputable def uF (h : UnitaryFieldData 2 f K) (n : ℕ) :
    ReflForm K (Fin n → K) :=
  unitaryForm 2 f (card_sq_of_unitary h) n

abbrev uS (h : UnitaryFieldData 2 f K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

abbrev uU (h : UnitaryFieldData 2 f K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

variable (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem uF_β (u v : Fin n → K) : (uF h n).β u v = ∑ i, (u i) ^ 2 ^ f * v i := by
  simp only [uF, unitaryForm_β, unitaryInvolution_apply]

theorem uF_σ (c : K) : (uF h n).σ c = h.bar c := by
  change unitaryInvolution K 2 f c = _
  rw [unitaryInvolution_apply, UnitaryFieldData.bar_apply]

theorem uF_symm (u v : Fin n → K) : (uF h n).β v u = (uF h n).σ ((uF h n).β u v) :=
  unitaryForm_symm (card_sq_of_unitary h) u v

theorem map_bar_eq_map_σ (A : Matrix (Fin n) (Fin n) K) :
    A.map h.bar = A.map (unitaryInvolution K 2 f) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply, UnitaryFieldData.bar_apply]

theorem uF_isometry_of_unitary {A : GL (Fin n) K} (hA : A ∈ uU h n) (u v : Fin n → K) :
    (uF h n).β ((A : Matrix (Fin n) (Fin n) K) *ᵥ u) ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (uF h n).β u v := by
  have h1 : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
    have := mem_primeFormUnitary.mp hA
    rwa [Units.val_one, Matrix.mul_one] at this
  rw [map_bar_eq_map_σ] at h1
  exact (unitaryForm_preserves_iff (card_sq_of_unitary h) _).mpr h1 u v

theorem uF_isometry_of_mem {A : GL (Fin n) K} (hA : A ∈ uS h n) (u v : Fin n → K) :
    (uF h n).β ((A : Matrix (Fin n) (Fin n) K) *ᵥ u) ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (uF h n).β u v :=
  uF_isometry_of_unitary h hA.1 u v

theorem isIsometric_uS : IsIsometric (uF h n) (natRep (uS h n)) := by
  intro g u v
  rw [natRep_apply, natRep_apply]
  exact uF_isometry_of_mem h g.2 u v

theorem tvMat_mulVec (a v : Fin n → K) :
    unitaryTransvection 2 f a 1 *ᵥ v = tv (uF h n) a v := by
  rw [unitaryTransvection_mulVec (card_sq_of_unitary h), one_mul, tv_apply]
  rfl

@[expose] noncomputable def tvGL {a : Fin n → K} (ha : (uF h n).β a a = 0) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (unitaryTransvection 2 f a 1)
    (by rw [unitaryTransvection_det (card_sq_of_unitary h) ha]; exact one_ne_zero)

theorem tvGL_mulVec {a : Fin n → K} (ha : (uF h n).β a a = 0) (v : Fin n → K) :
    ((tvGL h ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = tv (uF h n) a v :=
  tvMat_mulVec h a v

theorem tvGL_mem {a : Fin n → K} (ha : (uF h n).β a a = 0) : tvGL h ha ∈ uS h n := by
  refine ⟨?_, unitaryTransvection_det (card_sq_of_unitary h) ha 1⟩
  have hpres := unitaryTransvection_preserves (card_sq_of_unitary h) ha
    (c := 1) (by rw [map_one, CharTwo.neg_eq])
  have h1 := (unitaryForm_preserves_iff (card_sq_of_unitary h) _).mp hpres
  rw [← map_bar_eq_map_σ h] at h1
  change ((unitaryTransvection 2 f a 1).map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix _ _ K) *
    unitaryTransvection 2 f a 1 = ((1 : GL (Fin n) K) : Matrix _ _ K)
  rw [Units.val_one, Matrix.mul_one, h1]

@[expose] noncomputable def uPsi (A : GL (Fin n) K) (φ : K ≃+* K) :
    (Fin n → K) ≃+ (Fin n → K) where
  toFun v := (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i)
  invFun v := fun i => φ.symm ((((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) i)
  left_inv v := by
    funext i
    change φ.symm ((((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ fun j => φ (v j))) i) = v i
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact φ.symm_apply_apply (v i)
  right_inv v := by
    change (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (φ.symm _)) = v
    simp only [RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  map_add' u v := by
    change (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (u i + v i)) = _
    simp only [map_add]
    exact Matrix.mulVec_add _ _ _

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uPsi_apply (A : GL (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) :
    uPsi A φ v = (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i) :=
  rfl

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uPsi_smul (A : GL (Fin n) K) (φ : K ≃+* K) (c : K) (v : Fin n → K) :
    uPsi A φ (c • v) = φ c • uPsi A φ v := by
  rw [uPsi_apply, uPsi_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem uPsi_β {A : GL (Fin n) K} (hA : A ∈ uU h n) (φ : K ≃+* K) (u v : Fin n → K) :
    (uF h n).β (uPsi A φ u) (uPsi A φ v) = φ ((uF h n).β u v) := by
  rw [uPsi_apply, uPsi_apply, uF_isometry_of_unitary h hA, uF_β, uF_β, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_pow]

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem natRep_conj_uPsi (A : GL (Fin n) K) (φ : K ≃+* K) (g : GL (Fin n) K) (v : Fin n → K) :
    ((A * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ g * A⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v =
      uPsi A φ ((g : Matrix (Fin n) (Fin n) K) *ᵥ (uPsi A φ).symm v) := by
  rw [uPsi_apply]
  have hφ : (fun i => φ (((g : Matrix (Fin n) (Fin n) K) *ᵥ (uPsi A φ).symm v) i)) =
      ((g : Matrix (Fin n) (Fin n) K).map φ) *ᵥ (((A⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    funext i
    have := RingHom.map_mulVec (φ : K →+* K) (g : Matrix (Fin n) (Fin n) K)
      ((uPsi A φ).symm v) i
    rw [RingEquiv.coe_toRingHom] at this
    rw [this]
    congr 1
    funext j
    change φ (φ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  rw [hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, Matrix.mul_assoc]

theorem uPsi_tv {A : GL (Fin n) K} (hA : A ∈ uU h n) (φ : K ≃+* K) (a v : Fin n → K) :
    uPsi A φ (tv (uF h n) a ((uPsi A φ).symm v)) = tv (uF h n) (uPsi A φ a) v := by
  rw [tv_apply, tv_apply, map_add, uPsi_smul, AddEquiv.apply_symm_apply, ← uPsi_β h hA φ,
    AddEquiv.apply_symm_apply]

theorem conj_glAut_tvGL {A : GL (Fin n) K} (hA : A ∈ uU h n) (φ : K ≃+* K) {a : Fin n → K}
    (ha : (uF h n).β a a = 0) (hψa : uPsi A φ a = a) :
    A * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ (tvGL h ha) * A⁻¹ =
      tvGL h ha := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, natRep_conj_uPsi, tvGL_mulVec, uPsi_tv h hA,
    hψa, tvGL_mulVec]

@[expose] noncomputable def uIter (A : GL (Fin n) K) (φ : K ≃+* K) : ℕ → GL (Fin n) K
  | 0 => 1
  | j + 1 => A * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ (uIter A φ j)

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uIter_zero (A : GL (Fin n) K) (φ : K ≃+* K) : uIter A φ 0 = 1 :=
  rfl

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uIter_succ (A : GL (Fin n) K) (φ : K ≃+* K) (j : ℕ) :
    uIter A φ (j + 1) =
      A * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ (uIter A φ j) :=
  rfl

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uPsi_iterate (A : GL (Fin n) K) (φ : K ≃+* K) (j : ℕ) (v : Fin n → K) :
    (⇑(uPsi A φ))^[j] v = ((uIter A φ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      fun i => (φ ^ j) (v i) := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply, uIter_zero, Units.val_one, Matrix.one_mulVec]
    rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, uPsi_apply, uIter_succ, Units.val_mul,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    have := RingHom.map_mulVec (φ : K →+* K)
      ((uIter A φ j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (fun i => (φ ^ j) (v i)) i
    rw [RingEquiv.coe_toRingHom] at this
    rw [this, pow_succ']
    rfl

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem uIter_mem (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {A : GL (Fin n) K}
    (hA : A ∈ uU h n) (φ : K ≃+* K) (j : ℕ) : uIter A φ j ∈ uU h n := by
  induction j with
  | zero => exact one_mem _
  | succ j ih =>
    rw [uIter_succ]
    exact mul_mem hA (glAut_mem_primeFormUnitary h hC φ ih)

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem conj_field_pow (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {A : GL (Fin n) K}
    (hA : A ∈ uU h n) (φ : K ≃+* K) (j : ℕ) :
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨A, hA⟩ *
        primeFormFieldHom h hC φ) ^ j =
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          ⟨uIter A φ j, uIter_mem h hC hA φ j⟩ * primeFormFieldHom h hC (φ ^ j) := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero, map_one]
    have : (⟨uIter A φ 0, uIter_mem h hC hA φ 0⟩ : uU h n) = 1 := Subtype.ext rfl
    rw [this, map_one, mul_one]
  | succ j ih =>
    have hconj := primeFormField_conj_eq h hC φ ⟨uIter A φ j, uIter_mem h hC hA φ j⟩
    have hswap : primeFormFieldHom h hC φ *
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          ⟨uIter A φ j, uIter_mem h hC hA φ j⟩ =
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          (primeFormFieldU h hC φ ⟨uIter A φ j, uIter_mem h hC hA φ j⟩) *
          primeFormFieldHom h hC φ := by
      rw [← hconj, inv_mul_cancel_right]
    have hM : (⟨uIter A φ (j + 1), uIter_mem h hC hA φ (j + 1)⟩ : uU h n) =
        ⟨A, hA⟩ * primeFormFieldU h hC φ ⟨uIter A φ j, uIter_mem h hC hA φ j⟩ :=
      Subtype.ext rfl
    rw [pow_succ', ih, hM, map_mul, pow_succ', map_mul, mul_assoc, ← mul_assoc
      (primeFormFieldHom h hC φ), hswap]
    simp only [mul_assoc]

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
