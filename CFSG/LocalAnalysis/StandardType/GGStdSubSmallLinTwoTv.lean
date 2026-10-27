module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwoAlign

public section

namespace CFSG.StandardType.SmallL2

open Polynomial Matrix CoordSL CFSG.RankThree.CALinearPlane Multiplicative

@[expose] def trHom {F : Type*} [Field F] {s : ℕ} {i j : Fin s} (h : i ≠ j) :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin s) F where
  toFun c := Matrix.SpecialLinearGroup.transvection h (toAdd c)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    exact Matrix.SpecialLinearGroup.transvection_add h _ _

theorem tv_mulVec {F : Type*} [Field F] {s : ℕ} {i j : Fin s} (h : i ≠ j) (c : F)
    (v : Fin s → F) (m : Fin s) :
    ((Matrix.SpecialLinearGroup.transvection h c : Matrix (Fin s) (Fin s) F) *ᵥ v) m =
      v m + if m = i then c * v j else 0 := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  by_cases hm : m = i
  · subst hm
    simp
  · simp [hm]

theorem trHom_injective {F : Type*} [Field F] {s : ℕ} {i j : Fin s} (h : i ≠ j) :
    Function.Injective (trHom (F := F) h) := by
  intro a b hab
  have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin s) F =>
    (M : Matrix (Fin s) (Fin s) F) i j) hab
  simp only [trHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at h1
  simpa [h] using h1

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r : ℕ}
  (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {hC : (rootMat g).det = 1}

theorem nsSL_mul_theta_tv (hζ : AdjoinRoot.root g ^ 3 = 1) (k : Fin s → ℕ) {i j : Fin s}
    (h : i ≠ j) (c : AdjoinRoot g) :
    SLNS.nsSL ε hC k * theta g ε (Matrix.SpecialLinearGroup.transvection h c) =
      theta g ε (Matrix.SpecialLinearGroup.transvection h
        (AdjoinRoot.root g ^ k i * c * (AdjoinRoot.root g ^ 2) ^ k j)) * SLNS.nsSL ε hC k := by
  apply Subtype.ext
  change SLNS.nsMat ε (rootMat g) k * thetaMat g ε _ = thetaMat g ε _ * SLNS.nsMat ε (rootMat g) k
  rw [← thetaMat_diagonal, ← thetaMat_mul, ← thetaMat_mul]
  congr 1
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases hai : i = a
  · by_cases hbj : j = b
    · subst hai
      subst hbj
      simp only [and_self, if_true]
      have h3 : (AdjoinRoot.root g ^ 2) ^ k j * AdjoinRoot.root g ^ k j = 1 := by
        rw [← mul_pow, show AdjoinRoot.root g ^ 2 * AdjoinRoot.root g = AdjoinRoot.root g ^ 3 by
          ring, hζ, one_pow]
      calc AdjoinRoot.root g ^ k i * c
          = AdjoinRoot.root g ^ k i * c * ((AdjoinRoot.root g ^ 2) ^ k j *
              AdjoinRoot.root g ^ k j) := by rw [h3, mul_one]
        _ = _ := by ring
    · simp [hai, hbj]
  · simp [hai]

theorem theta_tv_mem_zeroBlock {p : ℕ} {β : Fin s → ZMod p} {i j : Fin s} (h : i ≠ j)
    (hi : β i = 0) (hj : β j = 0) (c : AdjoinRoot g) :
    theta g ε (Matrix.SpecialLinearGroup.transvection h c) ∈ coordBlockSL K (zeroCoords ε β) := by
  constructor
  · apply frameForm_injective g ε
    change frameForm g ε (compIndicator K (zeroCoords ε β) *
      thetaMat g ε (Matrix.SpecialLinearGroup.transvection h c : Matrix (Fin s) (Fin s) _)) =
        frameForm g ε (compIndicator K (zeroCoords ε β))
    rw [frameForm_mul, frameForm_compIndicator, frameForm_thetaMat]
    refine LinearMap.ext fun x => Prod.ext (funext fun m => ?_) rfl
    simp only [LinearMap.comp_apply, projN_apply, blockAct_apply, tv_mulVec]
    by_cases hm : m = i
    · subst hm
      simp [hi]
    · simp [hm]
  · apply frameForm_injective g ε
    change frameForm g ε (thetaMat g ε (Matrix.SpecialLinearGroup.transvection h c :
      Matrix (Fin s) (Fin s) _) * compIndicator K (zeroCoords ε β)) =
        frameForm g ε (compIndicator K (zeroCoords ε β))
    rw [frameForm_mul, frameForm_compIndicator, frameForm_thetaMat]
    refine LinearMap.ext fun x => Prod.ext (funext fun m => ?_) rfl
    simp only [LinearMap.comp_apply, projN_apply, blockAct_apply, tv_mulVec]
    by_cases hm : m = i
    · subst hm
      simp [hi, hj]
    · simp [hm]

section RootGroup

variable [CharP K 2] {G : Type} [Group G] (φ : Matrix.SpecialLinearGroup (Fin n) K →* G)

@[expose] noncomputable def rootHom {i j : Fin s} (h : i ≠ j) :
    Multiplicative (AdjoinRoot g) →* G :=
  φ.comp ((theta g ε).comp (trHom h))

theorem rootHom_apply {i j : Fin s} (h : i ≠ j) (x : Multiplicative (AdjoinRoot g)) :
    rootHom ε φ h x = φ (theta g ε (Matrix.SpecialLinearGroup.transvection h (toAdd x))) :=
  rfl

theorem rootHom_injective (hφ : Function.Injective φ) {i j : Fin s} (h : i ≠ j) :
    Function.Injective (rootHom ε φ h) :=
  hφ.comp ((theta_injective g ε).comp (trHom_injective h))

theorem rootHom_sq {i j : Fin s} (h : i ≠ j) (x : Multiplicative (AdjoinRoot g)) :
    rootHom ε φ h x ^ 2 = 1 := by
  rw [← map_pow]
  have : x ^ 2 = 1 := by
    apply toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    have := two_eq_zero_adjoinRoot (g := g)
    rw [← two_mul, this, zero_mul]
  rw [this, map_one]

theorem rootHom_conj {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
    {A₀ : Matrix.SpecialLinearGroup (Fin n) K} {hCp : rootMat g ^ 3 = 1}
    (hζ : AdjoinRoot.root g ^ 3 = 1) (t : Fin s → ZMod 3) {i j : Fin s} (h : i ≠ j)
    (c : AdjoinRoot g) :
    frameHom ψ A₀ ε hC hCp (ofAdd t) * rootHom ε (SLRep.ggFrame ψ A₀) h (ofAdd c) *
        (frameHom ψ A₀ ε hC hCp (ofAdd t))⁻¹ =
      rootHom ε (SLRep.ggFrame ψ A₀) h
        (ofAdd (AdjoinRoot.root g ^ (t i).val * c * (AdjoinRoot.root g ^ 2) ^ (t j).val)) := by
  rw [frameHom_eq_ggFrame, rootHom_apply, rootHom_apply, toAdd_ofAdd, toAdd_ofAdd,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  exact nsSL_mul_theta_tv ε hζ _ h c

end RootGroup

end CFSG.StandardType.SmallL2

end
