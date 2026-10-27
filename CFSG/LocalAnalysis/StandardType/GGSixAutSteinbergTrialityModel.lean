module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour

public section

namespace CFSG.StandardType

namespace Triality

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Field K]

abbrev Om8 (K : Type) [Field K] : Type := matrixDerived (coordinateQuadPlus 4 K)

noncomputable abbrev model8 : Sp8 K →* Om8 K := AutOm.spinModelPlus three_le_four

noncomputable abbrev X8 (γ : Fin 4 → ℤ) (c : K) : Om8 K := model8 (xr γ c)

theorem ext_X8 {G : Type*} [Group G] {f g : Om8 K →* G}
    (h : ∀ γ ∈ rootsD4, ∀ c : K, f (X8 γ c) = g (X8 γ c)) : f = g := by
  have h' : f.comp model8 = g.comp model8 := ext_xr fun γ hγ c => h γ hγ c
  refine MonoidHom.ext fun z => ?_
  obtain ⟨w, rfl⟩ := AutOm.spinModelPlus_surjective three_le_four z
  exact DFunLike.congr_fun h' w

theorem mulAut_ext_X8 {α β : MulAut (Om8 K)}
    (h : ∀ γ ∈ rootsD4, ∀ c : K, α (X8 γ c) = β (X8 γ c)) : α = β := by
  have h' := ext_X8 (f := α.toMonoidHom) (g := β.toMonoidHom) h
  exact MulEquiv.ext fun z => DFunLike.congr_fun h' z

theorem conjAct_eichler_eq₂ {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (g : similarityPairs Q)
    (hg : ∀ y, Q (coordinateSemilinearMap g.val y) = g.val.right (Q y)) (X Y : matrixDerived Q)
    {u w u' w' : Fin d → K}
    (hX : ∀ y, Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y =
      AutOm.eichlerC Q u w y)
    (hY : ∀ y, Matrix.mulVec ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y =
      AutOm.eichlerC Q u' w' y)
    (hu : coordinateSemilinearMap g.val u = u') (hw : coordinateSemilinearMap g.val w = w') :
    conjAct Q g X = Y :=
  AutOm.conjAct_apply_eq_of g X Y fun y => by
    rw [hX, hY, AutOm.semilinear_eichlerC Q g.val hg, hu, hw]

section CharTwo

variable [CharP K 2]

theorem repSign_cast (i j : Fin 4) (s t : Bool) : (repSign i j s t : K) = 1 :=
  intCast_eq_one_of_natAbs (by
    rcases repSign_eq_one_or_eq_neg_one i j s t with h | h <;> rw [h] <;> rfl)

theorem xr_eq_longRoot {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) :
    xr γ c = (plusFrame 4 K three_le_four).longRoot hij s t (.ofAdd c) := by
  rw [xr, SpinPlus.x, h, rootElt_eq _ hij rfl, repSign_cast, one_mul]

theorem X8_mulVec {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) (y : Fin (2 * 4) → K) :
    Matrix.mulVec ((X8 γ c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) y =
      AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec j t) (c • AutOm.pvec i s) y := by
  rw [X8, xr_eq_longRoot hij h, AutOm.spinModelPlus_longRoot_eichler]

theorem one_le_four : 1 ≤ 4 := by norm_num

theorem reflMat_pvec [Finite K] (k : Fin 4) (b : Bool) :
    Matrix.mulVec ((reflMat (coordinateQuadPlus 4 K) (AutOm.vPlus one_le_four)
      (AutOm.plusUnitVector_form_ne_zero one_le_four) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) (AutOm.pvec k b) = AutOm.pvec k (flip0 k b) := by
  by_cases hk : k = 0
  · subst hk
    rw [flip0, ite_eq_left rfl]
    exact AutOm.reflMat_vPlus_pvec_zero one_le_four b
  · rw [flip0, ite_eq_right hk]
    exact AutOm.reflMat_vPlus_pvec one_le_four (fun h => hk (h.trans rfl)) b

theorem plusRefl_X8 [Finite K] {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) :
    AutOm.plusRefl (K := K) one_le_four (X8 γ c) = X8 (refl0 γ) c := by
  obtain ⟨i, j, s, t, hij, h, -⟩ := exists_eq_fromStd hγ
  rw [AutOm.plusRefl_eq]
  refine conjAct_eichler_eq₂ _ (AutOm.gRefl_form _) _ _ (X8_mulVec hij h c)
    (X8_mulVec hij (toStdD_refl0_of_eq hij h) c) ?_ ?_
  · rw [AutOm.coordinateSemilinearMap_inclusion, reflMat_pvec]
  · rw [AutOm.coordinateSemilinearMap_inclusion, Matrix.mulVec_smul, reflMat_pvec]

theorem fieldAutP_X8 (σ : K ≃+* K) {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) :
    AutOm.fieldAutP 4 σ (X8 γ c) = X8 γ (σ c) := by
  obtain ⟨i, j, s, t, hij, h, -⟩ := exists_eq_fromStd hγ
  rw [AutOm.fieldAutP_eq]
  refine conjAct_eichler_eq₂ _ (AutOm.gField_form σ) _ _ (X8_mulVec hij h c)
    (X8_mulVec hij h (σ c)) ?_ ?_
  · rw [AutOm.coordinateSemilinearMap_fieldPair, AutOm.coordinateFieldMap_pvec]
  · rw [AutOm.coordinateSemilinearMap_fieldPair, coordinateFieldMap_smul,
      AutOm.coordinateFieldMap_pvec]

@[expose] noncomputable def modelEquiv8 : Sp8 K ≃* Om8 K :=
  MulEquiv.ofBijective model8 ⟨AutOm.spinModelPlus_injective three_le_four,
    AutOm.spinModelPlus_surjective three_le_four⟩

theorem modelEquiv8_apply (z : Sp8 K) : modelEquiv8 z = model8 z := rfl

variable [Finite K]

@[expose] noncomputable def theta : MulAut (Om8 K) := MulAut.congr modelEquiv8 triSpinAut

theorem theta_model (z : Sp8 K) : theta (model8 z) = model8 (triSpin z) := by
  rw [theta, ← modelEquiv8_apply, congr_apply_apply', modelEquiv8_apply, triSpinAut_apply]

theorem theta_X8 {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) : theta (X8 γ c) = X8 (tri γ) c := by
  rw [X8, theta_model, triSpin_xr hγ]

theorem theta_cube : (theta : MulAut (Om8 K)) ^ 3 = 1 := by
  rw [theta, ← map_pow, triSpinAut_cube, map_one]

theorem plusRefl_theta_plusRefl :
    AutOm.plusRefl (K := K) one_le_four * theta * AutOm.plusRefl one_le_four = theta⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv]
  refine mulAut_ext_X8 fun γ hγ c => ?_
  have h1 := tri_mem_roots hγ
  have h2 := refl0_mem_roots h1
  have h3 := tri_mem_roots h2
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, theta_X8 hγ, plusRefl_X8 h1,
    theta_X8 h2, plusRefl_X8 h3, refl0_tri_refl0_tri, MulAut.one_apply]

theorem theta_fieldAutP (σ : K ≃+* K) :
    theta * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * (theta : MulAut (Om8 K)) := by
  refine mulAut_ext_X8 fun γ hγ c => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, fieldAutP_X8 σ hγ, theta_X8 hγ, theta_X8 hγ,
    fieldAutP_X8 σ (tri_mem_roots hγ)]

theorem theta_plusRootElt {r : Om8 K} (hr : AutOm.PlusRootElt three_le_four r) :
    AutOm.PlusRootElt three_le_four (theta r) := by
  obtain ⟨i, j, hij, s, t, a, u, rfl⟩ := hr
  have hγ : fromStd (lv i j s t) ∈ rootsD4 :=
    mem_rootsD4_iff.2 ⟨i, j, hij, s, t, (roots_check i j s t hij).1⟩
  obtain ⟨i', j', s', t', hij', h', -⟩ := exists_eq_fromStd (tri_mem_roots hγ)
  have hL : (plusFrame 4 K three_le_four).longRoot hij s t (.ofAdd a) =
      xr (fromStd (lv i j s t)) a :=
    (xr_eq_longRoot hij (roots_check i j s t hij).1 a).symm
  refine ⟨i', j', hij', s', t', a, triSpin u, ?_⟩
  rw [theta_model, hL, map_mul triSpin, map_mul triSpin, map_inv (triSpin (K := K)),
    triSpin_xr hγ, xr_eq_longRoot hij' h']

end CharTwo

end Triality

end CFSG.StandardType
