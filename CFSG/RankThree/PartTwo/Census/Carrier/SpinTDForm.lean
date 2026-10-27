module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open QuadraticMap SpinFrame
open scoped Matrix

section Transform

variable {K L : Type} [Field K] [Field L] {ι ι' : Type} [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι']

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem polar_comp_of_map {Q : (ι → K) → K} {Q' : (ι' → L) → L} (f : K →+* L) (π : ι' ≃ ι)
    (hQ : ∀ v, Q' (f ∘ v ∘ π) = f (Q v)) (x y : ι → K) :
    polar Q' (f ∘ x ∘ π) (f ∘ y ∘ π) = f (polar Q x y) := by
  have hadd : f ∘ (x + y) ∘ π = f ∘ x ∘ π + f ∘ y ∘ π := by
    funext i
    simp
  simp only [polar, ← hadd, hQ, map_sub]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem eichler_comp_of_map {Q : QuadraticForm K (ι → K)} {Q' : QuadraticForm L (ι' → L)}
    (f : K →+* L) (π : ι' ≃ ι) (hQ : ∀ v, Q' (f ∘ v ∘ π) = f (Q v)) (u w x : ι → K) :
    eichler Q' (f ∘ u ∘ π) (f ∘ w ∘ π) (f ∘ x ∘ π) = f ∘ (eichler Q u w x) ∘ π := by
  have hpol := polar_comp_of_map (Q := ⇑Q) (Q' := ⇑Q') f π hQ
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu' : Q' (f ∘ u ∘ π) = 0 := by rw [hQ, h.1, map_zero]
    have hw' : polar Q' (f ∘ u ∘ π) (f ∘ w ∘ π) = 0 := by rw [hpol, h.2, map_zero]
    rw [eichler_apply hu' hw', eichler_apply h.1 h.2, hpol, hpol, hQ]
    funext i
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_add, map_sub, map_mul]
  · have h' : ¬(Q' (f ∘ u ∘ π) = 0 ∧ polar Q' (f ∘ u ∘ π) (f ∘ w ∘ π) = 0) := by
      rwa [hQ, hpol, map_eq_zero_iff f f.injective, map_eq_zero_iff f f.injective]
    rw [eichler_of_not h, eichler_of_not h']
    rfl

theorem toLinEquiv_symm_apply_entry (E : (ι → K) ≃ₗ[K] (ι → K)) (i j : ι) :
    (((toLinEquiv ι K).symm E : GL ι K) : Matrix ι ι K) i j = E (Pi.single j 1) i := by
  have h := toLinEquiv_apply ((toLinEquiv ι K).symm E) (Pi.single j 1)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, Matrix.mulVec_single_one, Matrix.col_apply]

theorem toLinEquiv_symm_eichler_map {Q : QuadraticForm K (ι → K)}
    {Q' : QuadraticForm L (ι' → L)} (f : K →+* L) (π : ι' ≃ ι)
    (hQ : ∀ v, Q' (f ∘ v ∘ π) = f (Q v)) (u w : ι → K) :
    ((((toLinEquiv ι K).symm (eichler Q u w) : GL ι K) : Matrix ι ι K).map f).submatrix π π =
      (((toLinEquiv ι' L).symm (eichler Q' (f ∘ u ∘ π) (f ∘ w ∘ π)) : GL ι' L) :
        Matrix ι' ι' L) := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.map_apply, toLinEquiv_symm_apply_entry,
    toLinEquiv_symm_apply_entry]
  have hj : (Pi.single j 1 : ι' → L) = f ∘ (Pi.single (π j) 1 : ι → K) ∘ π := by
    funext k
    simp only [Function.comp_apply, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp
  rw [hj, eichler_comp_of_map f π hQ]
  rfl

theorem eichler_isometry {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (Φ : V ≃ₗ[K] V')
    (hΦ : ∀ x, Q' (Φ x) = Q x) (u w : V) :
    (Φ.trans (eichler Q' (Φ u) (Φ w))).trans Φ.symm = eichler Q u w := by
  have hpol : ∀ x y, polar Q' (Φ x) (Φ y) = polar Q x y := fun x y => by
    simp only [polar, ← map_add, hΦ]
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu' : Q' (Φ u) = 0 := by rw [hΦ, h.1]
    have hw' : polar Q' (Φ u) (Φ w) = 0 := by rw [hpol, h.2]
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, eichler_apply hu' hw',
      eichler_apply h.1 h.2, hpol, hpol, hΦ, ← map_smul, ← map_smul, ← map_add, ← map_sub,
      LinearEquiv.symm_apply_apply]
  · have h' : ¬(Q' (Φ u) = 0 ∧ polar Q' (Φ u) (Φ w) = 0) := by rwa [hΦ, hpol]
    rw [eichler_of_not h, eichler_of_not h']
    refine LinearEquiv.ext fun x => ?_
    simp

end Transform

section Conj

variable {L : Type} [Field L] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] (Φ : (ι' → L) ≃ₗ[L] (ι → L))

@[expose] def conjGL : GL ι L →* GL ι' L where
  toFun A := (toLinEquiv ι' L).symm ((Φ.trans (toLinEquiv ι L A)).trans Φ.symm)
  map_one' := by
    apply (toLinEquiv ι' L).injective
    rw [MulEquiv.apply_symm_apply, map_one, map_one]
    exact LinearEquiv.ext fun x => by simp
  map_mul' A B := by
    apply (toLinEquiv ι' L).injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact LinearEquiv.ext fun x => by simp

theorem toLinEquiv_conjGL (A : GL ι L) :
    toLinEquiv ι' L (conjGL Φ A) = (Φ.trans (toLinEquiv ι L A)).trans Φ.symm :=
  MulEquiv.apply_symm_apply _ _

theorem conjGL_apply (A : GL ι L) (v : ι' → L) :
    ((conjGL Φ A : GL ι' L) : Matrix ι' ι' L) *ᵥ v = Φ.symm ((A : Matrix ι ι L) *ᵥ Φ v) := by
  rw [← toLinEquiv_apply, toLinEquiv_conjGL]
  rfl

theorem conjGL_injective : Function.Injective (conjGL Φ) := by
  intro A B h
  have h' := congrArg (toLinEquiv ι' L) h
  rw [toLinEquiv_conjGL, toLinEquiv_conjGL] at h'
  apply (toLinEquiv ι L).injective
  refine LinearEquiv.ext fun x => ?_
  have := LinearEquiv.congr_fun h' (Φ.symm x)
  simpa using this

theorem map_conjGL_entry (θ : L →+* L) (τ : Equiv.Perm ι) (hτ : τ.symm = τ)
    (hΦ : ∀ v, Φ (θ ∘ v) = (θ ∘ Φ v) ∘ τ) (A : GL ι L)
    (hA : ((A : Matrix ι ι L).map θ).submatrix τ τ = A) (i j : ι') :
    θ ((conjGL Φ A : GL ι' L) i j) = (conjGL Φ A : GL ι' L) i j := by
  have hτ2 : ∀ a, τ (τ a) = a := fun a => by
    have h := τ.symm_apply_apply a
    rwa [hτ] at h
  have hΦinv : ∀ y, Φ.symm ((θ ∘ y) ∘ τ) = θ ∘ Φ.symm y := fun y => by
    apply Φ.injective
    rw [LinearEquiv.apply_symm_apply, hΦ, LinearEquiv.apply_symm_apply]
  have hAmap : (A : Matrix ι ι L).map θ = (A : Matrix ι ι L).submatrix τ τ := by
    conv_rhs => rw [← hA]
    ext a b
    simp [hτ2]
  have hAv : ∀ x, (A : Matrix ι ι L) *ᵥ ((θ ∘ x) ∘ τ) = (θ ∘ ((A : Matrix ι ι L) *ᵥ x)) ∘ τ := by
    intro x
    have h1 : θ ∘ ((A : Matrix ι ι L) *ᵥ x) = ((A : Matrix ι ι L).map θ) *ᵥ (θ ∘ x) := by
      funext k
      exact RingHom.map_mulVec θ _ x k
    rw [h1, hAmap, Matrix.submatrix_mulVec_equiv, hτ]
    funext k
    simp [hτ2]
  have hcol : ∀ v, θ ∘ (((conjGL Φ A : GL ι' L) : Matrix ι' ι' L) *ᵥ v) =
      ((conjGL Φ A : GL ι' L) : Matrix ι' ι' L) *ᵥ (θ ∘ v) := by
    intro v
    rw [conjGL_apply, conjGL_apply, hΦ, hAv, hΦinv]
  have hsingle : θ ∘ (Pi.single j 1 : ι' → L) = Pi.single j 1 := by
    funext k
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have h := congrFun (hcol (Pi.single j 1)) i
  rw [hsingle, Matrix.mulVec_single_one, Function.comp_apply, Matrix.col_apply] at h
  exact h

end Conj

section Lift

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Subfield L)
  {G : Type*} [Group G] (φ : G →* GL ι L) (hφ : ∀ g i j, (φ g : Matrix ι ι L) i j ∈ S)

@[expose] def liftMat (g : G) : Matrix ι ι S :=
  fun i j => ⟨(φ g : Matrix ι ι L) i j, hφ g i j⟩

theorem map_liftMat (g : G) : (liftMat S φ hφ g).map S.subtype = (φ g : Matrix ι ι L) := by
  ext i j
  rfl

theorem liftMat_mul (g h : G) : liftMat S φ hφ g * liftMat S φ hφ h = liftMat S φ hφ (g * h) := by
  apply Matrix.map_injective (f := S.subtype) S.subtype_injective
  simp only
  rw [Matrix.map_mul, map_liftMat, map_liftMat, map_liftMat, map_mul, Units.val_mul]

theorem liftMat_one : liftMat S φ hφ 1 = 1 := by
  apply Matrix.map_injective (f := S.subtype) S.subtype_injective
  simp only
  rw [map_liftMat, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] def liftGL : G →* GL ι S where
  toFun g := ⟨liftMat S φ hφ g, liftMat S φ hφ g⁻¹, by rw [liftMat_mul, mul_inv_cancel,
    liftMat_one], by rw [liftMat_mul, inv_mul_cancel, liftMat_one]⟩
  map_one' := Units.ext (liftMat_one S φ hφ)
  map_mul' g h := Units.ext (liftMat_mul S φ hφ g h).symm

theorem map_liftGL (g : G) :
    Matrix.GeneralLinearGroup.map S.subtype (liftGL S φ hφ g) = φ g :=
  Units.ext (map_liftMat S φ hφ g)

theorem coe_liftGL_apply (g : G) (i j : ι) :
    (((liftGL S φ hφ g : GL ι S) : Matrix ι ι S) i j : L) = (φ g : Matrix ι ι L) i j :=
  rfl

theorem liftGL_injective (h : Function.Injective φ) : Function.Injective (liftGL S φ hφ) := by
  intro g g' hg
  apply h
  rw [← map_liftGL S φ hφ, ← map_liftGL S φ hφ, hg]

end Lift

abbrev MI (m : ℕ) : Type :=
  Fin m ⊕ Fin m ⊕ Fin 2

section Phi

variable {L : Type} [Field L] {m : ℕ}

@[expose] def phiV (ω ω' : L) (v : MI m → L) : DI (m + 1) → L
  | .inl i => Fin.lastCases (v (.inr (.inr 0)) - ω * v (.inr (.inr 1))) (fun j => v (.inl j)) i
  | .inr i =>
      Fin.lastCases (v (.inr (.inr 0)) - ω' * v (.inr (.inr 1))) (fun j => v (.inr (.inl j))) i

@[expose] def phiInv (ω ω' : L) (w : DI (m + 1) → L) : MI m → L
  | .inl j => w (.inl j.castSucc)
  | .inr (.inl j) => w (.inr j.castSucc)
  | .inr (.inr t) => ![(ω' * w (.inl (Fin.last m)) - ω * w (.inr (Fin.last m))) / (ω' - ω),
      (w (.inl (Fin.last m)) - w (.inr (Fin.last m))) / (ω' - ω)] t

@[simp] theorem phiV_inl_castSucc (ω ω' : L) (v : MI m → L) (j : Fin m) :
    phiV ω ω' v (.inl j.castSucc) = v (.inl j) := by
  simp [phiV]

@[simp] theorem phiV_inr_castSucc (ω ω' : L) (v : MI m → L) (j : Fin m) :
    phiV ω ω' v (.inr j.castSucc) = v (.inr (.inl j)) := by
  simp [phiV]

@[simp] theorem phiV_inl_last (ω ω' : L) (v : MI m → L) :
    phiV ω ω' v (.inl (Fin.last m)) = v (.inr (.inr 0)) - ω * v (.inr (.inr 1)) := by
  simp [phiV]

@[simp] theorem phiV_inr_last (ω ω' : L) (v : MI m → L) :
    phiV ω ω' v (.inr (Fin.last m)) = v (.inr (.inr 0)) - ω' * v (.inr (.inr 1)) := by
  simp [phiV]

section Plane

variable {ω ω' : L} (hne : ω' - ω ≠ 0)
include hne

theorem plane_inv₁ (a b : L) : (ω' * a - ω * b) / (ω' - ω) - ω * ((a - b) / (ω' - ω)) = a := by
  field_simp
  ring

theorem plane_inv₂ (a b : L) : (ω' * a - ω * b) / (ω' - ω) - ω' * ((a - b) / (ω' - ω)) = b := by
  field_simp
  ring

theorem plane_inv₃ (u t : L) : (ω' * (u - ω * t) - ω * (u - ω' * t)) / (ω' - ω) = u := by
  field_simp
  ring

theorem plane_inv₄ (u t : L) : (u - ω * t - (u - ω' * t)) / (ω' - ω) = t := by
  field_simp
  ring

end Plane

@[expose] def phi (ω ω' : L) (hω : ω ≠ ω') : (MI m → L) ≃ₗ[L] (DI (m + 1) → L) where
  toFun := phiV ω ω'
  invFun := phiInv ω ω'
  map_add' v w := by
    funext x
    rcases x with i | i <;> induction i using Fin.lastCases <;> simp <;> ring
  map_smul' c v := by
    funext x
    rcases x with i | i <;> induction i using Fin.lastCases <;> simp <;> ring
  left_inv v := by
    have hne : ω' - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω)
    funext x
    rcases x with j | j | t
    · simp [phiInv]
    · simp [phiInv]
    · fin_cases t
      · simp only [phiInv, phiV_inl_last, phiV_inr_last]
        exact plane_inv₃ hne _ _
      · simp only [phiInv, phiV_inl_last, phiV_inr_last]
        exact plane_inv₄ hne _ _
  right_inv w := by
    have hne : ω' - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω)
    funext x
    rcases x with i | i <;> induction i using Fin.lastCases
    · simp only [phiV_inl_last, phiInv]
      exact plane_inv₁ hne _ _
    · simp [phiInv]
    · simp only [phiV_inr_last, phiInv]
      exact plane_inv₂ hne _ _
    · simp [phiInv]

theorem phi_apply (ω ω' : L) (hω : ω ≠ ω') (v : MI m → L) : phi ω ω' hω v = phiV ω ω' v :=
  rfl

theorem statedQuadMinus_eq (b c : L) (v : MI m → L) :
    StatedQuadMinus (m + 1) L b c v = ∑ i : Fin m, v (.inl i) * v (.inr (.inl i)) +
      v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2 :=
  rfl

theorem statedQuadPlus_phiV (ω ω' : L) (v : MI m → L) :
    StatedQuadPlus (m + 1) L (phiV ω ω' v) = StatedQuadMinus (m + 1) L (-(ω + ω')) (ω * ω') v := by
  rw [statedQuadMinus_eq]
  simp only [StatedQuadPlus, Fin.sum_univ_castSucc, phiV_inl_castSucc, phiV_inr_castSucc,
    phiV_inl_last, phiV_inr_last]
  ring

theorem quadPlus_phi (ω ω' : L) (hω : ω ≠ ω') (v : MI m → L) :
    quadPlus (m + 1) L (phi ω ω' hω v) = quadMinus (m + 1) L (-(ω + ω')) (ω * ω') v := by
  rw [coe_quadPlus, coe_quadMinus, phi_apply]
  exact statedQuadPlus_phiV ω ω' v

abbrev tauM (m : ℕ) : Equiv.Perm (DI (m + 1)) :=
  Equiv.swap (.inl (Fin.last m)) (.inr (Fin.last m))

theorem phiV_comp (ω ω' : L) (θ : L →+* L) (hθ : θ ω = ω') (hθ' : θ ω' = ω) (v : MI m → L) :
    phiV ω ω' (θ ∘ v) = (θ ∘ phiV ω ω' v) ∘ tauM m := by
  funext x
  have hθv : ∀ y : L, ∀ z : L, θ (y - ω' * z) = θ y - ω * θ z := fun y z => by
    rw [map_sub, map_mul, hθ']
  have hθv' : ∀ y : L, ∀ z : L, θ (y - ω * z) = θ y - ω' * θ z := fun y z => by
    rw [map_sub, map_mul, hθ]
  rcases x with i | i
  · induction i using Fin.lastCases with
    | last =>
      simp only [Function.comp_apply, phiV_inl_last, Equiv.swap_apply_left, phiV_inr_last, hθv]
    | cast j =>
      have h1 : (Sum.inl j.castSucc : DI (m + 1)) ≠ .inl (Fin.last m) := fun h =>
        Fin.castSucc_ne_last j (Sum.inl_injective h)
      have h2 : (Sum.inl j.castSucc : DI (m + 1)) ≠ .inr (Fin.last m) := Sum.inl_ne_inr
      simp only [Function.comp_apply, phiV_inl_castSucc, Equiv.swap_apply_of_ne_of_ne h1 h2]
  · induction i using Fin.lastCases with
    | last =>
      simp only [Function.comp_apply, phiV_inr_last, Equiv.swap_apply_right, phiV_inl_last, hθv']
    | cast j =>
      have h3 : (Sum.inr j.castSucc : DI (m + 1)) ≠ .inl (Fin.last m) := Sum.inr_ne_inl
      have h4 : (Sum.inr j.castSucc : DI (m + 1)) ≠ .inr (Fin.last m) := fun h =>
        Fin.castSucc_ne_last j (Sum.inr_injective h)
      simp only [Function.comp_apply, phiV_inr_castSucc, Equiv.swap_apply_of_ne_of_ne h3 h4]

end Phi

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD
