module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOm8Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.StandardType.D4Rank
open CFSG.RankThree.PartOne.AUTSL
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Matrix

private noncomputable def s16kOm8AddEquiv {K : Type} [Field K] (g : Om8 K) :
    (Fin (2 * 4) → K) ≃+ (Fin (2 * 4) → K) where
  toFun v := act g v
  invFun v := act g⁻¹ v
  left_inv v := by
    show act g⁻¹ (act g v) = v
    rw [← act_mul g⁻¹ g v, inv_mul_cancel, act_one]
  right_inv v := by
    show act g (act g⁻¹ v) = v
    rw [← act_mul g g⁻¹ v, mul_inv_cancel, act_one]
  map_add' v w := by
    show act g (v + w) = act g v + act g w
    simp only [act, Matrix.mulVec_add]

private noncomputable def s16kOm8MatAddEquiv {K : Type} [Field K] (r : GL (Fin (2 * 4)) K) :
    (Fin (2 * 4) → K) ≃+ (Fin (2 * 4) → K) where
  toFun v := r.val *ᵥ v
  invFun v := (r⁻¹).val *ᵥ v
  left_inv v := by
    show (r⁻¹).val *ᵥ (r.val *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv v := by
    show r.val *ᵥ ((r⁻¹).val *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add r.val v w

@[expose] def om8Stab (K : Type) [Field K] : Subgroup (MulAut (Om8 K)) where
  carrier := {a | Om8TwistIso 1 a}
  one_mem' := by
    refine ⟨AddEquiv.refl _, ?_⟩
    intro x v
    simp only [AddEquiv.refl_apply, MulAut.one_apply]
  mul_mem' := by
    rintro a b ⟨Ta, hTa⟩ ⟨Tb, hTb⟩
    have hTa' : ∀ x v, Ta (act x v) = act (a x) (Ta v) := fun x v => by
      simpa only [MulAut.one_apply] using hTa x v
    have hTb' : ∀ x v, Tb (act x v) = act (b x) (Tb v) := fun x v => by
      simpa only [MulAut.one_apply] using hTb x v
    refine ⟨Tb.trans Ta, ?_⟩
    intro x v
    rw [MulAut.one_apply, MulAut.mul_apply, AddEquiv.trans_apply, hTb' x v,
      hTa' (b x) (Tb v)]
    rfl
  inv_mem' := by
    rintro a ⟨T, hT⟩
    have hT' : ∀ x v, T (act x v) = act (a x) (T v) := fun x v => by
      simpa only [MulAut.one_apply] using hT x v
    refine ⟨T.symm, ?_⟩
    intro x v
    rw [MulAut.one_apply, MulAut.inv_apply]
    have h := hT' (a⁻¹ x) (T.symm v)
    rw [MulAut.apply_inv_self, T.apply_symm_apply] at h
    exact T.symm_apply_eq.mpr h.symm

theorem inner_le_om8Stab (K : Type) [Field K] : inner (Om8 K) ≤ om8Stab K := by
  change (MulAut.conj : Om8 K →* MulAut (Om8 K)).range ≤ om8Stab K
  rintro _ ⟨g, rfl⟩
  refine ⟨s16kOm8AddEquiv g, ?_⟩
  intro x v
  rw [MulAut.one_apply, MulAut.conj_apply]
  change act g (act x v) = act (g * x * g⁻¹) (act g v)
  rw [← act_mul g x v, ← act_mul (g * x * g⁻¹) g v]
  congr 1
  group

theorem plusRefl_mem_om8Stab (K : Type) [Field K] [Finite K] [CharP K 2] :
    (AutOm.plusRefl (K := K) one_le_four) ∈ om8Stab K := by
  let r : GL (Fin (2 * 4)) K :=
    reflMat (coordinateQuadPlus 4 K) (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four)
      (AutOm.plusUnitVector_form_ne_zero one_le_four)
  refine ⟨s16kOm8MatAddEquiv r, ?_⟩
  intro x v
  change r.val *ᵥ (act x v) = act (AutOm.plusRefl (K := K) one_le_four x) (r.val *ᵥ v)
  have hval : ((AutOm.plusRefl (K := K) one_le_four x : Om8 K) : GL (Fin (2 * 4)) K) =
      r * (x : GL (Fin (2 * 4)) K) * r⁻¹ := by
    change ((reflAut (coordinateQuadPlus 4 K)
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four)
      (AutOm.plusUnitVector_form_ne_zero one_le_four) x : Om8 K) : GL (Fin (2 * 4)) K) =
      reflMat (coordinateQuadPlus 4 K)
        (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four)
        (AutOm.plusUnitVector_form_ne_zero one_le_four) * (x : GL (Fin (2 * 4)) K) *
        (reflMat (coordinateQuadPlus 4 K)
          (CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four)
          (AutOm.plusUnitVector_form_ne_zero one_le_four))⁻¹
    exact reflAut_apply_val _ _ x
  rw [act, act]
  have hkey : ((AutOm.plusRefl (K := K) one_le_four x : Om8 K) : GL (Fin (2 * 4)) K) * r =
      r * (x : GL (Fin (2 * 4)) K) := by
    rw [hval, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  have hmat : (((AutOm.plusRefl (K := K) one_le_four x : Om8 K) :
        GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * r.val =
      r.val * ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
    rw [← Units.val_mul, hkey, Units.val_mul]
  rw [Matrix.mulVec_mulVec v r.val ((x : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K),
      Matrix.mulVec_mulVec v (((AutOm.plusRefl (K := K) one_le_four x : Om8 K) :
        GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) r.val,
      hmat]

theorem theta_not_mem_om8Stab (K : Type) [Field K] [Finite K] [CharP K 2] :
    (theta : MulAut (Om8 K)) ∉ om8Stab K := by
  intro h
  change Om8TwistIso 1 (theta : MulAut (Om8 K)) at h
  obtain ⟨T, hT⟩ := h
  have hT' : ∀ x v, T (act x v) = act (theta x) (T v) := fun x v => by
    simpa only [MulAut.one_apply] using hT x v
  let e : LinearMap.ker (omRep (x0 (K := K)) - 1) ≃
      LinearMap.ker (omRep (theta (x0 (K := K))) - 1) :=
    { toFun := fun v => ⟨T v, (mem_ker_iff_act (x := theta (x0 (K := K)))).mpr
        (by rw [← hT' (x0 (K := K)) v,
          (mem_ker_iff_act (x := x0 (K := K))).mp v.2])⟩
      invFun := fun w => ⟨T.symm w, (mem_ker_iff_act (x := x0 (K := K))).mpr
        (T.injective (by
          rw [hT' (x0 (K := K)) (T.symm w), T.apply_symm_apply,
            (mem_ker_iff_act (x := theta (x0 (K := K)))).mp w.2]))⟩
      left_inv := fun v => Subtype.ext (T.symm_apply_apply v)
      right_inv := fun w => Subtype.ext (T.apply_symm_apply w) }
  have hcard := Nat.card_congr e
  rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (omRep (x0 (K := K)) - 1)),
    Module.natCard_eq_pow_finrank (K := K)
      (V := LinearMap.ker (omRep (theta (x0 (K := K))) - 1))] at hcard
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd := Nat.pow_right_injective h2 hcard
  have hd' : omFixDim (x0 (K := K)) = omFixDim (theta (x0 (K := K))) := hd
  rw [omFixDim_x0, omFixDim_theta_x0] at hd'
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
