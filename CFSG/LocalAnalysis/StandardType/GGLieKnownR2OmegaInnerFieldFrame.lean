module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSettingW
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalTorus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCoreO2

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.LieKnownR2.POmega.Radical
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

@[expose] def GGSiegelWIrreducible {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (P P' : HypPair Q) : Prop :=
  ∀ X : Submodule K V, X ≤ siegelW Q P.e P'.e P.f P'.f →
    (∀ g ∈ elementaryGroup Q, (∀ v ∈ Submodule.span K {P.e, P'.e, P.f, P'.f}, g v = v) →
      ∀ x ∈ X, g x ∈ X) →
    X = ⊥ ∨ X = siegelW Q P.e P'.e P.f P'.f

private noncomputable def ifield_T {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (v : ι → F) : ι → F :=
  A.val *ᵥ (fun i => φ (v i))

private noncomputable def ifield_Tinv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (v : ι → F) : ι → F :=
  fun i => φ.symm ((A⁻¹.val *ᵥ v) i)

private lemma ifield_T_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (c : F) (x : ι → F) :
    ifield_T A φ (c • x) = φ c • ifield_T A φ x := by
  have h : (fun i => φ ((c • x) i)) = φ c • (fun i => φ (x i)) := by
    funext i; simp
  unfold ifield_T
  rw [← Matrix.mulVec_smul, h]

private lemma ifield_T_Tinv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (v : ι → F) : ifield_T A φ (ifield_Tinv A φ v) = v := by
  have h : (fun i => φ (φ.symm ((A⁻¹.val *ᵥ v) i))) = A⁻¹.val *ᵥ v := by
    funext i; simp
  unfold ifield_T ifield_Tinv
  rw [h, Matrix.mulVec_mulVec,
    show (A.val * A⁻¹.val : Matrix ι ι F) = 1 from Units.mul_inv A, Matrix.one_mulVec]

private lemma ifield_Tinv_T {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (v : ι → F) : ifield_Tinv A φ (ifield_T A φ v) = v := by
  unfold ifield_Tinv ifield_T
  funext i
  have h : (A⁻¹.val *ᵥ (A.val *ᵥ (fun j => φ (v j)))) i = φ (v i) := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [h]
  simp

private lemma ifield_Tinv_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (x y : ι → F) :
    ifield_Tinv A φ (x + y) = ifield_Tinv A φ x + ifield_Tinv A φ y := by
  funext i
  simp only [ifield_Tinv, Pi.add_apply]
  rw [Matrix.mulVec_add]
  simp

private lemma ifield_Tinv_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (c : F) (x : ι → F) :
    ifield_Tinv A φ (c • x) = φ.symm c • ifield_Tinv A φ x := by
  funext i
  simp only [ifield_Tinv, Pi.smul_apply]
  rw [Matrix.mulVec_smul]
  simp

private lemma ifield_Tinv_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (φ : F ≃+* F) (x y : ι → F) :
    ifield_Tinv A φ (x - y) = ifield_Tinv A φ x - ifield_Tinv A φ y := by
  have hneg : ifield_Tinv A φ (-y) = -ifield_Tinv A φ y := by
    funext i
    simp only [ifield_Tinv, Pi.neg_apply]
    rw [Matrix.mulVec_neg]
    simp
  rw [sub_eq_add_neg, ifield_Tinv_add, hneg, sub_eq_add_neg]

private lemma ifield_T_spinAction {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ}
    {y : MulAut ↥(spinGroup Q)} (hmat : GGMatrixSemilinearAction Q A φ μ y)
    (x : ↥(spinGroup Q)) (v : ι → F) :
    spinAction Q (y x) (ifield_T A φ v) = ifield_T A φ (spinAction Q x v) := by
  change spinAction Q (y x) (A.val *ᵥ (fun i => φ (v i))) =
    A.val *ᵥ (fun i => φ (spinAction Q x v i))
  rw [← spinMatrix_mulVec, ← spinMatrix_mulVec, hmat x]
  have hφ : (fun i => φ ((((spinMatrix Q x : GL ι F) : Matrix ι ι F) *ᵥ v) i)) =
      (((glFieldEquiv ι φ (spinMatrix Q x) : GL ι F) : Matrix ι ι F) *ᵥ
        (fun i => φ (v i))) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, glFieldEquiv_entry]
  have hA : (A⁻¹.val * A.val : Matrix ι ι F) = 1 := Units.inv_mul A
  rw [hφ, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc, hA, Matrix.mul_one, ← Matrix.mulVec_mulVec]

private lemma ifield_Tinv_spinAction {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ}
    {y : MulAut ↥(spinGroup Q)} (hmat : GGMatrixSemilinearAction Q A φ μ y)
    (x : ↥(spinGroup Q)) (v : ι → F) :
    spinAction Q (y⁻¹ x) (ifield_Tinv A φ v) = ifield_Tinv A φ (spinAction Q x v) := by
  have h := ifield_T_spinAction (Q := Q) hmat (y⁻¹ x) (ifield_Tinv A φ v)
  rw [show y (y⁻¹ x) = x from by simp, ifield_T_Tinv] at h
  rw [h, ifield_Tinv_T]

private lemma ifield_siegelRoot_map {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hS : SpinOmegaData Q) (P P' : HypPair Q) :
    (siegelRoot Q P.e P'.e).map (spinAction Q) = siegelGroup Q P.e P'.e := by
  have hsiegel_le : siegelGroup Q P.e P'.e ≤ elementaryGroup Q := by
    rw [siegelGroup, Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    exact eichler_mem_elementaryGroup Q _ _
  rw [siegelRoot, Subgroup.map_comap_eq, hS.range_eq]
  exact inf_eq_right.mpr hsiegel_le

private lemma ifield_Tinv_mem_siegelY {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2]
    {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q) {P P' : HypPair Q} (h : P.Orth P')
    {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ} {y : MulAut ↥(spinGroup Q)}
    (hyR : (siegelRoot Q P.e P'.e).map y.toMonoidHom = siegelRoot Q P.e P'.e)
    (hmat : GGMatrixSemilinearAction Q A φ μ y) :
    ∀ x ∈ siegelY F P.e P'.e, ifield_Tinv A φ x ∈ siegelY F P.e P'.e := by
  have hR_img := ifield_siegelRoot_map (Q := Q) hS P P'
  have hmem_inv : ∀ a, a ∈ siegelRoot Q P.e P'.e → y⁻¹ a ∈ siegelRoot Q P.e P'.e := by
    intro a ha
    have hcontra : a ∈ (siegelRoot Q P.e P'.e).map y.toMonoidHom := by rw [hyR]; exact ha
    obtain ⟨b, hb, hba⟩ := hcontra
    have hb' : b = y⁻¹ a := by
      apply y.injective
      show (MulEquiv.toMonoidHom y) b = y (y⁻¹ a)
      rw [hba]
      simp
    rw [← hb']
    exact hb
  intro x hx
  rw [← siegelMovedSpace_eq (Q := Q) (P := P) (P' := P') h] at hx
  rw [← siegelMovedSpace_eq (Q := Q) (P := P) (P' := P') h]
  induction hx using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨g, hg, v, rfl⟩ := hw
      obtain ⟨x', hx', rfl⟩ := (show g ∈ (siegelRoot Q P.e P'.e).map (spinAction Q) from by
        rw [hR_img]; exact hg)
      rw [ifield_Tinv_sub, ← ifield_Tinv_spinAction (Q := Q) hmat x' v]
      have hx'' : y⁻¹ x' ∈ siegelRoot Q P.e P'.e := hmem_inv x' hx'
      have hmem : spinAction Q (y⁻¹ x') ∈ siegelGroup Q P.e P'.e := by
        rw [← hR_img]; exact ⟨y⁻¹ x', hx'', rfl⟩
      exact Submodule.subset_span ⟨spinAction Q (y⁻¹ x'), hmem, ifield_Tinv A φ v, rfl⟩
  | zero =>
      rw [show ifield_Tinv A φ 0 = 0 by funext i; simp [ifield_Tinv]]
      exact Submodule.zero_mem _
  | add x z _ _ ihx ihz =>
      rw [ifield_Tinv_add]
      exact Submodule.add_mem _ ihx ihz
  | smul c x _ ih =>
      rw [ifield_Tinv_smul]
      exact Submodule.smul_mem _ _ ih

theorem fieldPart_eq_one_frame {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ} (hsim : GGSemilinearSimilitude Q A φ μ)
    {y : MulAut ↥(spinGroup Q)}
    (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    (hmat : GGMatrixSemilinearAction Q A φ μ y) :
    ∀ x : F, φ x = x := by
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero]
  · let lam : Fˣ := Units.mk0 x hx
    obtain ⟨s, hsE, hse, hse', hsf, hsf', hsw⟩ :=
      siegelTorus_exists (Q := Q) (P := P) (P' := P') h lam
    have hsr : s ∈ (Spin.spinAction Q).range := by rw [hS.range_eq]; exact hsE
    obtain ⟨ŝ, hŝ⟩ := hsr
    obtain ⟨hyR, htriv2⟩ := htriv
    have hstab : ∀ v ∈ siegelY F P.e P'.e, spinAction Q ŝ v ∈ siegelY F P.e P'.e := by
      intro v hv
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
      rw [map_add, map_smul, map_smul, hŝ, hse, hse']
      exact Submodule.add_mem _
        (Submodule.smul_mem _ c (Submodule.smul_mem _ (lam : F) (Submodule.subset_span (by simp))))
        (Submodule.smul_mem _ d (Submodule.smul_mem _ (lam : F) (Submodule.subset_span (by simp))))
    have hN : ŝ ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q)) :=
      stab_le_normalizer_siegelRoot (Q := Q) (P := P) (P' := P') h hstab
    have hcore : y ŝ * ŝ⁻¹ ∈ orthSiegelCore Q P.e P'.e :=
      siegelO2_le_orthSiegelCore (Q := Q) hS h hV hW (htriv2 ŝ hN)
    have hfix := orthSiegelCore_fixes_Y (Q := Q) (P := P) (P' := P') h hcore
    have hw : spinAction Q (ŝ⁻¹) P.e = (lam : F)⁻¹ • P.e := by
      have hu : spinAction Q ŝ ((lam : F)⁻¹ • P.e) = P.e := by
        rw [map_smul, hŝ, hse, smul_smul, inv_mul_cancel₀ lam.ne_zero, one_smul]
      have h1 : (spinAction Q ŝ)⁻¹ (spinAction Q ŝ ((lam : F)⁻¹ • P.e)) =
          (lam : F)⁻¹ • P.e := LinearEquiv.inv_apply_apply' _ _
      rw [hu] at h1
      rw [map_inv]
      exact h1
    have hcongr_scalar : spinAction Q (y ŝ) P.e = (lam : F) • P.e := by
      have hcalc : spinAction Q (y ŝ * ŝ⁻¹) P.e = spinAction Q (y ŝ) ((lam : F)⁻¹ • P.e) := by
        rw [map_mul, LinearEquiv.mul_apply, hw]
      have hfixP : spinAction Q (y ŝ * ŝ⁻¹) P.e = P.e :=
        hfix P.e (Submodule.subset_span (by simp))
      have h2 : spinAction Q (y ŝ) ((lam : F)⁻¹ • P.e) = P.e := by
        rw [← hcalc]; exact hfixP
      have h3 : (lam : F)⁻¹ • spinAction Q (y ŝ) P.e = P.e := by
        simpa using h2
      calc spinAction Q (y ŝ) P.e
          = (lam : F) • ((lam : F)⁻¹ • spinAction Q (y ŝ) P.e) := by
              rw [smul_smul, mul_inv_cancel₀ lam.ne_zero, one_smul]
        _ = (lam : F) • P.e := by rw [h3]
    have hw_mem : ifield_Tinv A φ P.e ∈ siegelY F P.e P'.e :=
      ifield_Tinv_mem_siegelY (Q := Q) hS h hyR hmat P.e (Submodule.subset_span (by simp))
    have hsp : ∀ w ∈ siegelY F P.e P'.e, spinAction Q ŝ w = (lam : F) • w := by
      intro w hwv
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hwv
      rw [map_add, map_smul, map_smul, hŝ, hse, hse']
      module
    have hsp_w := hsp (ifield_Tinv A φ P.e) hw_mem
    have hkey : spinAction Q (y ŝ) P.e = φ (lam : F) • P.e := by
      calc spinAction Q (y ŝ) P.e
          = spinAction Q (y ŝ) (ifield_T A φ (ifield_Tinv A φ P.e)) := by
              rw [ifield_T_Tinv]
        _ = ifield_T A φ (spinAction Q ŝ (ifield_Tinv A φ P.e)) :=
              ifield_T_spinAction (Q := Q) hmat ŝ (ifield_Tinv A φ P.e)
        _ = ifield_T A φ ((lam : F) • ifield_Tinv A φ P.e) := by rw [hsp_w]
        _ = φ (lam : F) • ifield_T A φ (ifield_Tinv A φ P.e) :=
              ifield_T_smul A φ (lam : F) (ifield_Tinv A φ P.e)
        _ = φ (lam : F) • P.e := by rw [ifield_T_Tinv]
    have hfinal : φ (lam : F) • P.e = (lam : F) • P.e := hkey.symm.trans hcongr_scalar
    have hphi : φ (lam : F) = (lam : F) := smul_left_injective F P.e_ne_zero hfinal
    exact hphi

end CFSG.StandardType.LieKnownR2.POmega.Inner
