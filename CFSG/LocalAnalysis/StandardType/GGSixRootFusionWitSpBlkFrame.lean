module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkNorm
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkExt
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusForm
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameMatrix
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNs

public section

open Matrix Module

namespace CFSG.StandardType

namespace WitSpBlk

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {K : Type} [Field K] {n e s r : ℕ}

@[expose] noncomputable def frameΦ (A₀ : GL (Fin n ⊕ Fin n) K)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) :
    ((Fin s → Fin e → K) × (Fin r → K)) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
  (SpNS.dCoords (Pi.basisFun K (Fin e)) (Equiv.refl (Fin s)) (Equiv.refl (Fin r))).trans
    ((LinearEquiv.funCongrLeft K K ε).trans (Matrix.GeneralLinearGroup.toLin A₀).toLinearEquiv)

theorem frameΦ_apply (A₀ : GL (Fin n ⊕ Fin n) K) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (d : Fin s → Fin e → K) (w : Fin r → K) :
    frameΦ A₀ ε (d, w) = (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      (SpNS.dCoords (Pi.basisFun K (Fin e)) (Equiv.refl (Fin s)) (Equiv.refl (Fin r)) (d, w) ∘
        ε) := rfl

theorem toMatrix_toLin' (C : Matrix (Fin e) (Fin e) K) :
    LinearMap.toMatrix (Pi.basisFun K (Fin e)) (Pi.basisFun K (Fin e)) (Matrix.toLin' C) = C := by
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem toLin'_pow_apply (C : Matrix (Fin e) (Fin e) K) (m : ℕ) (z : Fin e → K) :
    (Matrix.toLin' C ^ m) z = (C ^ m) *ᵥ z := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_pow]

theorem mat_mulVec_frameΦ {A₀ : GL (Fin n ⊕ Fin n) K}
    {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) K}
    {X : StatedSp n K} {k : Fin s → ℕ} (hX : RootPlaneSp.SpBlockMat A₀ ε C X k)
    (d : Fin s → Fin e → K) (w : Fin r → K) :
    mat n K X *ᵥ frameΦ A₀ ε (d, w) = frameΦ A₀ ε (fun i => (Matrix.toLin' C ^ k i) (d i), w) := by
  have hAA : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmul := SpNS.dCoords_mul (Pi.basisFun K (Fin e)) (Equiv.refl (Fin s)) (Equiv.refl (Fin r))
    (Matrix.toLin' C) k d w
  rw [toMatrix_toLin'] at hmul
  rw [frameΦ_apply, frameΦ_apply, mat_apply, hX, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, hAA, Matrix.mul_one, ← Matrix.mulVec_mulVec, submatrix_mulVec_equiv,
    Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, hmul]
  rfl

theorem jForm_eq_form (u v : Fin n ⊕ Fin n → K) : SpNS.jForm n K u v = form u v := by
  rw [SpNS.jForm_apply]
  rfl

theorem frameΦ_form {A₀ : GL (Fin n ⊕ Fin n) K}
    {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) K}
    (hreal : ∀ k : Fin s → ℕ, ∃ X : StatedSp n K, RootPlaneSp.SpBlockMat A₀ ε C X k)
    (k : Fin s → ℕ) (d d' : Fin s → Fin e → K) (w w' : Fin r → K) :
    SpNS.jForm n K (frameΦ A₀ ε (fun i => (Matrix.toLin' C ^ k i) (d i), w))
        (frameΦ A₀ ε (fun i => (Matrix.toLin' C ^ k i) (d' i), w')) =
      SpNS.jForm n K (frameΦ A₀ ε (d, w)) (frameΦ A₀ ε (d', w')) := by
  obtain ⟨X, hX⟩ := hreal k
  rw [jForm_eq_form, jForm_eq_form, ← mat_mulVec_frameΦ hX, ← mat_mulVec_frameΦ hX, form_mulVec]

theorem toLin'_sub_surj {C : Matrix (Fin e) (Fin e) K} (hC : IsUnit (C - 1)) (z : Fin e → K) :
    ∃ z₀, Matrix.toLin' C z₀ - z₀ = z := by
  obtain ⟨u, hu⟩ := hC
  refine ⟨((u⁻¹ : (Matrix (Fin e) (Fin e) K)ˣ) : Matrix (Fin e) (Fin e) K) *ᵥ z, ?_⟩
  rw [Matrix.toLin'_apply]
  have h1 : C *ᵥ (((u⁻¹ : (Matrix (Fin e) (Fin e) K)ˣ) : Matrix (Fin e) (Fin e) K) *ᵥ z) -
      ((u⁻¹ : (Matrix (Fin e) (Fin e) K)ˣ) : Matrix (Fin e) (Fin e) K) *ᵥ z =
      (C - 1) *ᵥ (((u⁻¹ : (Matrix (Fin e) (Fin e) K)ˣ) : Matrix (Fin e) (Fin e) K) *ᵥ z) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h1, ← hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

@[expose] noncomputable def blockForm (A₀ : GL (Fin n ⊕ Fin n) K)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (i : Fin s) :
    LinearMap.BilinForm K (Fin e → K) :=
  SpNS.frameBlockForm (SpNS.jForm n K) (frameΦ A₀ ε) i

variable {A₀ : GL (Fin n ⊕ Fin n) K} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
  {C : Matrix (Fin e) (Fin e) K}

theorem blockForm_apply (i : Fin s) (z z' : Fin e → K) :
    blockForm A₀ ε i z z' =
      form (frameΦ A₀ ε (Pi.single i z, 0)) (frameΦ A₀ ε (Pi.single i z', 0)) := by
  rw [blockForm, SpNS.frameBlockForm_apply, jForm_eq_form]

theorem blockForm_isAlt (i : Fin s) : (blockForm A₀ ε i).IsAlt := fun z => by
  rw [blockForm_apply, form_self]

theorem pow_single_apply (i : Fin s) (z : Fin e → K) (j : Fin s) :
    (Matrix.toLin' C ^ (Pi.single i 1 : Fin s → ℕ) j) ((Pi.single i z : Fin s → Fin e → K) j) =
      (Pi.single i (C *ᵥ z) : Fin s → Fin e → K) j := by
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

theorem mat_mulVec_frameΦ_same {X : StatedSp n K} {i : Fin s}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X (Pi.single i 1)) (z : Fin e → K) :
    mat n K X *ᵥ frameΦ A₀ ε (Pi.single i z, 0) = frameΦ A₀ ε (Pi.single i (C *ᵥ z), 0) := by
  rw [mat_mulVec_frameΦ hX]
  congr 2
  funext j
  exact pow_single_apply i z j

theorem form_eq_zero_of_form {v : Fin n ⊕ Fin n → K}
    (hv : ∀ u : Fin n ⊕ Fin n → K, form v u = 0) : v = 0 :=
  SpNS.jForm_nondegenerate.1 v fun u => by rw [jForm_eq_form, hv]

theorem blockForm_mulVec
    (hreal : ∀ k : Fin s → ℕ, ∃ X : StatedSp n K, RootPlaneSp.SpBlockMat A₀ ε C X k)
    (i : Fin s) (z z' : Fin e → K) :
    blockForm A₀ ε i (C *ᵥ z) (C *ᵥ z') = blockForm A₀ ε i z z' := by
  have h := frameΦ_form hreal (Pi.single i 1) (Pi.single i z) (Pi.single i z') 0 0
  have e1 : (fun j => (Matrix.toLin' C ^ (Pi.single i 1 : Fin s → ℕ) j)
      ((Pi.single i z : Fin s → Fin e → K) j)) = Pi.single i (C *ᵥ z) :=
    funext (pow_single_apply i z)
  have e2 : (fun j => (Matrix.toLin' C ^ (Pi.single i 1 : Fin s → ℕ) j)
      ((Pi.single i z' : Fin s → Fin e → K) j)) = Pi.single i (C *ᵥ z') :=
    funext (pow_single_apply i z')
  rw [e1, e2, jForm_eq_form, jForm_eq_form] at h
  rw [blockForm_apply, blockForm_apply, h]

section Geometry

variable (hC : IsUnit (C - 1))
  (hreal : ∀ k : Fin s → ℕ, ∃ X : StatedSp n K, RootPlaneSp.SpBlockMat A₀ ε C X k)
include hC hreal

theorem form_frameΦ_single (i : Fin s) (z : Fin e → K) (d : Fin s → Fin e → K)
    (w : Fin r → K) :
    form (frameΦ A₀ ε (Pi.single i z, 0)) (frameΦ A₀ ε (d, w)) = blockForm A₀ ε i z (d i) := by
  have e : frameΦ A₀ ε (d, w) =
      frameΦ A₀ ε (Pi.single i (d i), 0) + frameΦ A₀ ε (d - Pi.single i (d i), w) := by
    rw [← map_add, Prod.mk_add_mk, add_sub_cancel, zero_add]
  have h0 := SpNS.frame_orth_single (toLin'_sub_surj hC) (frameΦ_form hreal) i z
    (d := d - Pi.single i (d i)) w (by simp)
  rw [jForm_eq_form] at h0
  rw [e, form_add_right, h0, add_zero, blockForm_apply]

theorem blockForm_nondegenerate (i : Fin s) : (blockForm A₀ ε i).Nondegenerate := by
  have hrefl : (blockForm A₀ ε i).IsRefl := (blockForm_isAlt i).isRefl
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).2 fun z hz => ?_
  have h1 : frameΦ A₀ ε (Pi.single i z, 0) = 0 := by
    refine form_eq_zero_of_form fun u => ?_
    obtain ⟨⟨d, w⟩, rfl⟩ := (frameΦ A₀ ε).surjective u
    rw [form_frameΦ_single hC hreal, hz]
  have h2 : ((Pi.single i z : Fin s → Fin e → K), (0 : Fin r → K)) = 0 :=
    (frameΦ A₀ ε).injective (h1.trans (map_zero _).symm)
  have h3 := congrArg (fun x : (Fin s → Fin e → K) × (Fin r → K) => x.1 i) h2
  simpa using h3

theorem fix_of_orth {i : Fin s} {X : StatedSp n K}
    (hX : RootPlaneSp.SpBlockMat A₀ ε C X (Pi.single i 1)) {v : Fin n ⊕ Fin n → K}
    (hv : ∀ z, form (frameΦ A₀ ε (Pi.single i z, 0)) v = 0) : mat n K X *ᵥ v = v := by
  obtain ⟨⟨d, w⟩, rfl⟩ := (frameΦ A₀ ε).surjective v
  have hd : d i = 0 := (blockForm_nondegenerate hC hreal i).2 _ fun z => by
    rw [← form_frameΦ_single hC hreal, hv]
  rw [mat_mulVec_frameΦ hX]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj
    simp [hd]
  · simp [Pi.single_eq_of_ne hj]

end Geometry

end WitSpBlk

end CFSG.StandardType
