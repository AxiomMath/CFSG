module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Sylow
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG
  CFSG.Assembly.LowTwoRank QuadraticMap
open scoped Matrix

namespace L613C3

variable {K : Type} [Field K]

section Vec

@[expose] noncomputable def ePart (v : Fin (2 * 4) → K) : Fin 3 → K := fun j => v (ie j.castSucc)

@[expose] noncomputable def fPart (v : Fin (2 * 4) → K) : Fin 3 → K := fun j => v (jf j.castSucc)

theorem ePart_add (v w : Fin (2 * 4) → K) : ePart (v + w) = ePart v + ePart w := rfl
theorem fPart_add (v w : Fin (2 * 4) → K) : fPart (v + w) = fPart v + fPart w := rfl
theorem ePart_smul (c : K) (v : Fin (2 * 4) → K) : ePart (c • v) = c • ePart v := rfl
theorem fPart_smul (c : K) (v : Fin (2 * 4) → K) : fPart (c • v) = c • fPart v := rfl

@[expose] noncomputable def leviVec (A : Matrix.SpecialLinearGroup (Fin 3) K)
    (v : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  fun i => Sum.elim
    (Fin.snoc ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ ePart v) (v (ie (Fin.last 3))) : Fin 4 → K)
    (Fin.snoc (fPart v ᵥ* ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) (v (jf (Fin.last 3))) : Fin 4 → K)
    ((plusIndexEquiv 4).symm i)

variable (A : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin (2 * 4) → K)

theorem leviVec_ie_castSucc (l : Fin 3) :
    leviVec A v (ie l.castSucc) = ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ ePart v) l := by
  simp only [leviVec, Equiv.symm_apply_apply, Sum.elim_inl]
  exact Fin.snoc_castSucc (α := fun _ => K) _ _ _

theorem leviVec_ie_last : leviVec A v (ie (Fin.last 3)) = v (ie (Fin.last 3)) := by
  simp only [leviVec, Equiv.symm_apply_apply, Sum.elim_inl]
  exact Fin.snoc_last (α := fun _ => K) _ _

theorem leviVec_jf_castSucc (l : Fin 3) :
    leviVec A v (jf l.castSucc) = (fPart v ᵥ* ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) l := by
  simp only [leviVec, Equiv.symm_apply_apply, Sum.elim_inr]
  exact Fin.snoc_castSucc (α := fun _ => K) _ _ _

theorem leviVec_jf_last : leviVec A v (jf (Fin.last 3)) = v (jf (Fin.last 3)) := by
  simp only [leviVec, Equiv.symm_apply_apply, Sum.elim_inr]
  exact Fin.snoc_last (α := fun _ => K) _ _

theorem ePart_leviVec : ePart (leviVec A v) = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ePart v :=
  funext fun l => leviVec_ie_castSucc A v l

theorem fPart_leviVec : fPart (leviVec A v) =
    fPart v ᵥ* ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  funext fun l => leviVec_jf_castSucc A v l

omit A v [Field K] in
theorem vec_ext {v w : Fin (2 * 4) → K}
    (he : ∀ l : Fin 3, v (ie l.castSucc) = w (ie l.castSucc))
    (h3 : v (ie (Fin.last 3)) = w (ie (Fin.last 3)))
    (hf : ∀ l : Fin 3, v (jf l.castSucc) = w (jf l.castSucc))
    (h3' : v (jf (Fin.last 3)) = w (jf (Fin.last 3))) : v = w := by
  funext i
  rcases ie_or_jf i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · induction k using Fin.lastCases with
    | last => exact h3
    | cast l => exact he l
  · induction k using Fin.lastCases with
    | last => exact h3'
    | cast l => exact hf l

omit v in
theorem leviVec_add (v w : Fin (2 * 4) → K) : leviVec A (v + w) = leviVec A v + leviVec A w := by
  refine vec_ext (fun l => ?_) ?_ (fun l => ?_) ?_ <;>
    simp only [Pi.add_apply, leviVec_ie_castSucc, leviVec_ie_last, leviVec_jf_castSucc,
      leviVec_jf_last, ePart_add, fPart_add, Matrix.mulVec_add, Matrix.add_vecMul]

omit v in
theorem leviVec_smul (c : K) (v : Fin (2 * 4) → K) : leviVec A (c • v) = c • leviVec A v := by
  refine vec_ext (fun l => ?_) ?_ (fun l => ?_) ?_ <;>
    simp only [Pi.smul_apply, smul_eq_mul, leviVec_ie_castSucc, leviVec_ie_last,
      leviVec_jf_castSucc, leviVec_jf_last, ePart_smul, fPart_smul, Matrix.mulVec_smul,
      Matrix.smul_vecMul]

omit A v in
theorem leviVec_mul (A B : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin (2 * 4) → K) :
    leviVec (A * B) v = leviVec A (leviVec B v) := by
  refine vec_ext (fun l => ?_) ?_ (fun l => ?_) ?_
  · rw [leviVec_ie_castSucc, leviVec_ie_castSucc, ePart_leviVec, Matrix.mulVec_mulVec,
      Matrix.SpecialLinearGroup.coe_mul]
  · rw [leviVec_ie_last, leviVec_ie_last, leviVec_ie_last]
  · rw [leviVec_jf_castSucc, leviVec_jf_castSucc, fPart_leviVec, Matrix.vecMul_vecMul, mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul]
  · rw [leviVec_jf_last, leviVec_jf_last, leviVec_jf_last]

omit A in
theorem leviVec_one : leviVec (1 : Matrix.SpecialLinearGroup (Fin 3) K) v = v := by
  refine vec_ext (fun l => ?_) ?_ (fun l => ?_) ?_
  · rw [leviVec_ie_castSucc, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rfl
  · rw [leviVec_ie_last]
  · rw [leviVec_jf_castSucc, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    rfl
  · rw [leviVec_jf_last]

theorem Q_leviVec : coordinateQuadPlus 4 K (leviVec A v) = coordinateQuadPlus 4 K v := by
  rw [coordQ_apply, coordQ_apply, Fin.sum_univ_castSucc (n := 3), Fin.sum_univ_castSucc (n := 3),
    leviVec_ie_last, leviVec_jf_last]
  congr 1
  simp only [leviVec_ie_castSucc, leviVec_jf_castSucc]
  have h : ∑ l : Fin 3, ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ ePart v) l *
      (fPart v ᵥ* ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) l =
      (fPart v ᵥ* ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⬝ᵥ
        ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ ePart v) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [h, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one, dotProduct]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Vec

section Hom

@[expose] noncomputable def leviLin (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K) where
  toFun := leviVec A
  map_add' := leviVec_add A
  map_smul' := leviVec_smul A

theorem leviLin_apply (A : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin (2 * 4) → K) :
    leviLin A v = leviVec A v := rfl

@[expose] noncomputable def leviHom :
    Matrix.SpecialLinearGroup (Fin 3) K →* ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) where
  toFun A := LinearEquiv.ofLinearMap (leviLin A) (leviLin A⁻¹)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, leviLin_apply, leviLin_apply, ← leviVec_mul, mul_inv_cancel,
        leviVec_one, LinearMap.id_apply])
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, leviLin_apply, leviLin_apply, ← leviVec_mul, inv_mul_cancel,
        leviVec_one, LinearMap.id_apply])
  map_one' := LinearEquiv.ext fun v => leviVec_one v
  map_mul' A B := LinearEquiv.ext fun v => leviVec_mul A B v

theorem leviHom_apply (A : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin (2 * 4) → K) :
    leviHom A v = leviVec A v := rfl

@[expose] noncomputable def leviGL : Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin (2 * 4)) K :=
  matrixLinearIso.symm.toMonoidHom.comp leviHom

theorem leviGL_mulVec (A : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin (2 * 4) → K) :
    (leviGL A : GL (Fin (2 * 4)) K).val *ᵥ v = leviVec A v := by
  change (matrixLinearIso.symm (leviHom A) : GL (Fin (2 * 4)) K).val *ᵥ v = _
  rw [symm_mulVec, leviHom_apply]

theorem leviGL_mem_isometries (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    leviGL A ∈ matrixIsometries (coordinateQuadPlus 4 K) := by
  rw [mem_matrixIsometries_iff]
  intro v
  change coordinateQuadPlus 4 K (matrixLinearEquiv (matrixLinearIso.symm (leviHom A)) v) = _
  rw [← matrixLinearIso_apply_eq, MulEquiv.apply_symm_apply, leviHom_apply, Q_leviVec]

theorem range_leviGL_le : (leviGL (K := K)).range ≤ matrixDerived (coordinateQuadPlus 4 K) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have hperf : ⁅(leviGL (K := K)).range, (leviGL (K := K)).range⁆ = (leviGL (K := K)).range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
  have hiso : (leviGL (K := K)).range ≤ matrixIsometries (coordinateQuadPlus 4 K) := by
    rintro _ ⟨A, rfl⟩
    exact leviGL_mem_isometries A
  calc (leviGL (K := K)).range = ⁅(leviGL (K := K)).range, (leviGL (K := K)).range⁆ := hperf.symm
    _ ≤ ⁅matrixIsometries (coordinateQuadPlus 4 K), matrixIsometries (coordinateQuadPlus 4 K)⁆ :=
        Subgroup.commutator_mono hiso hiso
    _ = matrixDerived (coordinateQuadPlus 4 K) := rfl

@[expose] noncomputable def leviOm : Matrix.SpecialLinearGroup (Fin 3) K →* Om8 K :=
  (leviGL (K := K)).codRestrict (matrixDerived (coordinateQuadPlus 4 K))
    fun A => range_leviGL_le ⟨A, rfl⟩

theorem act_leviOm (A : Matrix.SpecialLinearGroup (Fin 3) K) (v : Fin (2 * 4) → K) :
    act (leviOm A) v = leviVec A v :=
  leviGL_mulVec A v

theorem commutator_range_leviOm :
    ⁅(leviOm (K := K)).range, (leviOm (K := K)).range⁆ = (leviOm (K := K)).range := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)

end Hom

section Scalar

@[expose] noncomputable def scalarSL {c : K} (hc : c ^ 3 = 1) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨c • (1 : Matrix (Fin 3) (Fin 3) K), by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, hc]⟩

theorem coe_scalarSL {c : K} (hc : c ^ 3 = 1) :
    ((scalarSL hc : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (1 : Matrix (Fin 3) (Fin 3) K) := rfl

theorem inv_scalarSL {c : K} (hc : c ^ 3 = 1) (hc' : c⁻¹ ^ 3 = 1) :
    (scalarSL hc)⁻¹ = scalarSL hc' := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarSL, coe_scalarSL,
    Matrix.SpecialLinearGroup.coe_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  rw [mul_inv_cancel₀ hc0, one_smul]

theorem scalarSL_comm {c : K} (hc : c ^ 3 = 1) (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A * scalarSL hc = scalarSL hc * A := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_scalarSL,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

variable [Finite K] [CharP K 2]

theorem leviOm_scalar {ω : Kˣ} (hω3 : ω ^ 3 = 1) :
    leviOm (scalarSL (c := (ω : K)) (by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one])) =
      zStd ω := by
  have hc : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hc' : ((ω : K))⁻¹ ^ 3 = 1 := by rw [inv_pow, hc, inv_one]
  refine om8_ext fun v => ?_
  rw [act_leviOm, zStd, act_dg]
  refine vec_ext (fun l => ?_) ?_ (fun l => ?_) ?_
  · rw [leviVec_ie_castSucc, coe_scalarSL, Matrix.smul_mulVec, Matrix.one_mulVec, twHom_ie,
      ite_eq_right (castSucc_ne_three l)]
    rfl
  · rw [leviVec_ie_last, twHom_ie, ite_eq_left last_eq_three, Units.val_one, one_mul]
  · rw [leviVec_jf_castSucc, inv_scalarSL hc hc', coe_scalarSL, Matrix.vecMul_smul,
      Matrix.vecMul_one, twHom_jf, ite_eq_right (castSucc_ne_three l), Units.val_inv_eq_inv_val]
    rfl
  · rw [leviVec_jf_last, twHom_jf, ite_eq_left last_eq_three, inv_one, Units.val_one, one_mul]

omit [CharP K 2] in
theorem card_specialLinear_le :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) ≤ 3 * Nat.card (StatedProj (StatedSL 3 K)) := by
  rw [(Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 3) K)).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 3 K).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, Fintype.card_fin, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _))

omit [CharP K 2] in
theorem card_range_leviOm_le :
    Nat.card (leviOm (K := K)).range ≤ 3 * Nat.card (StatedProj (StatedSL 3 K)) :=
  (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans
    card_specialLinear_le

end Scalar

end L613C3

end CFSG.StandardType
