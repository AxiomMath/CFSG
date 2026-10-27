module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}
private noncomputable def w1369_autHom {W : Type} [CommGroup W] {n : ℕ}
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)) (h : MulAut W) :
    (Fin n → GaloisField 2 2) →+ (Fin n → GaloisField 2 2) where
  toFun v := Multiplicative.toAdd (ψ (h (ψ.symm (Multiplicative.ofAdd v))))
  map_zero' := by simp
  map_add' v w := by
    show Multiplicative.toAdd (ψ (h (ψ.symm (Multiplicative.ofAdd (v + w))))) =
      Multiplicative.toAdd (ψ (h (ψ.symm (Multiplicative.ofAdd v)))) +
        Multiplicative.toAdd (ψ (h (ψ.symm (Multiplicative.ofAdd w))))
    simp only [ofAdd_add, map_mul, toAdd_mul]

@[simp] private lemma w1369_autHom_apply {W : Type} [CommGroup W] {n : ℕ}
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)) (h : MulAut W)
    (v : Fin n → GaloisField 2 2) :
    w1369_autHom ψ h v =
      Multiplicative.toAdd (ψ (h (ψ.symm (Multiplicative.ofAdd v)))) := rfl

private lemma w1369_autHom_comp {W : Type} [CommGroup W] {n : ℕ}
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)) (h1 h2 : MulAut W) :
    w1369_autHom ψ (h1 * h2) = (w1369_autHom ψ h1).comp (w1369_autHom ψ h2) := by
  apply AddMonoidHom.ext
  intro v
  simp only [AddMonoidHom.comp_apply, w1369_autHom_apply, ofAdd_toAdd,
    ψ.symm_apply_apply]
  rfl

private lemma w1369_autHom_one {W : Type} [CommGroup W] {n : ℕ}
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)) :
    w1369_autHom ψ (1 : MulAut W) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro v
  simp only [w1369_autHom_apply, AddMonoidHom.id_apply]
  rw [show (1 : MulAut W) (ψ.symm (Multiplicative.ofAdd v)) =
    ψ.symm (Multiplicative.ofAdd v) from rfl, ψ.apply_symm_apply,
    toAdd_ofAdd]

private lemma w1369_autHom_smul {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    {h : MulAut W} (hcomm : ∀ x : ↥X, h * (x : MulAut W) = (x : MulAut W) * h)
    (x : ↥X) (v : Fin n → GaloisField 2 2) :
    w1369_autHom ψ h (cOf x • v) = cOf x • w1369_autHom ψ h v := by
  set w : W := ψ.symm (Multiplicative.ofAdd v) with hw
  have hv : Multiplicative.toAdd (ψ w) = v := by
    rw [hw, ψ.apply_symm_apply]
    rfl
  have h1 : Multiplicative.ofAdd (cOf x • v) = ψ ((x : MulAut W) w) := by
    rw [← hv, hcOf x w]
  have h2 : ψ.symm (Multiplicative.ofAdd (cOf x • v)) = (x : MulAut W) w := by
    rw [h1, ψ.symm_apply_apply]
  have hTv : w1369_autHom ψ h v = Multiplicative.toAdd (ψ (h w)) := by
    rw [w1369_autHom_apply, ← hw]
  have hstep : h ((x : MulAut W) w) = (x : MulAut W) (h w) := by
    rw [← MulAut.mul_apply, hcomm x, MulAut.mul_apply]
  calc w1369_autHom ψ h (cOf x • v)
      = Multiplicative.toAdd (ψ (h ((x : MulAut W) w))) := by
        rw [w1369_autHom_apply, h2]
    _ = Multiplicative.toAdd (ψ ((x : MulAut W) (h w))) := by rw [hstep]
    _ = cOf x • Multiplicative.toAdd (ψ (h w)) := by
        rw [hcOf x (h w)]
        rfl
    _ = cOf x • w1369_autHom ψ h v := by rw [hTv]

private noncomputable def w1369_autLin {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (h : MulAut W) (hcomm : ∀ x : ↥X, h * (x : MulAut W) = (x : MulAut W) * h) :
    (Fin n → GaloisField 2 2) →ₗ[GaloisField 2 2] (Fin n → GaloisField 2 2) where
  toFun := w1369_autHom ψ h
  map_add' := (w1369_autHom ψ h).map_add
  map_smul' := by
    intro c v
    by_cases hc : c = 0
    · simp [hc]
    · obtain ⟨x, rfl⟩ := hcOf_surj c hc
      exact w1369_autHom_smul hcOf hcomm x v

private noncomputable def w1369_linEquiv {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (h : MulAut W) (hcomm : ∀ x : ↥X, h * (x : MulAut W) = (x : MulAut W) * h) :
    (Fin n → GaloisField 2 2) ≃ₗ[GaloisField 2 2] (Fin n → GaloisField 2 2) :=
  LinearEquiv.ofLinearMap (w1369_autLin hcOf hcOf_surj h hcomm)
    (w1369_autLin hcOf hcOf_surj h⁻¹ (fun x => by
      have hx := hcomm x
      calc h⁻¹ * (x : MulAut W) = h⁻¹ * ((x : MulAut W) * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * (x : MulAut W)) * h⁻¹ := by rw [← hx]
        _ = (x : MulAut W) * h⁻¹ := by group))
    (by
      apply LinearMap.ext
      intro v
      change w1369_autHom ψ h (w1369_autHom ψ h⁻¹ v) = v
      have hcomp := congrArg (fun f : (Fin n → GaloisField 2 2) →+ _ => f v)
        (w1369_autHom_comp (ψ := ψ) h h⁻¹)
      simpa [mul_inv_cancel, w1369_autHom_one] using hcomp.symm)
    (by
      apply LinearMap.ext
      intro v
      change w1369_autHom ψ h⁻¹ (w1369_autHom ψ h v) = v
      have hcomp := congrArg (fun f : (Fin n → GaloisField 2 2) →+ _ => f v)
        (w1369_autHom_comp (ψ := ψ) h⁻¹ h)
      simpa [inv_mul_cancel, w1369_autHom_one] using hcomp.symm)

private noncomputable def w1369_lambda {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (H : Subgroup (MulAut W))
    (hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W)) :
    ↥H →* ((Fin n → GaloisField 2 2) ≃ₗ[GaloisField 2 2]
      (Fin n → GaloisField 2 2)) where
  toFun h := w1369_linEquiv hcOf hcOf_surj (h : MulAut W) (hcommH h)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change w1369_autHom ψ (1 : MulAut W) v = v
    rw [w1369_autHom_one]
    rfl
  map_mul' h1 h2 := by
    apply LinearEquiv.ext
    intro v
    change w1369_autHom ψ ((h1 : MulAut W) * (h2 : MulAut W)) v =
      w1369_autHom ψ (h1 : MulAut W) (w1369_autHom ψ (h2 : MulAut W) v)
    have hcomp := congrArg (fun f : (Fin n → GaloisField 2 2) →+ _ => f v)
      (w1369_autHom_comp (ψ := ψ) (h1 : MulAut W) (h2 : MulAut W))
    simpa using hcomp

private noncomputable def w1369_theta {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (H : Subgroup (MulAut W))
    (hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W)) :
    ↥H →* Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2) :=
  (Matrix.GeneralLinearGroup.toLin).symm.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (GaloisField 2 2)
        (Fin n → GaloisField 2 2)).symm.toMonoidHom.comp
      (w1369_lambda hcOf hcOf_surj H hcommH))

private lemma w1369_theta_apply {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (H : Subgroup (MulAut W))
    (hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W))
    (h : ↥H) (v : Fin n → GaloisField 2 2) :
    (w1369_theta hcOf hcOf_surj H hcommH h :
        Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec v =
      w1369_autHom ψ (h : MulAut W) v := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.toLin_apply]
  simp only [w1369_theta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change w1369_autHom ψ (h : MulAut W) v = w1369_autHom ψ (h : MulAut W) v
  rfl

private lemma w1369_theta_injective {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (H : Subgroup (MulAut W))
    (hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W)) :
    Function.Injective (w1369_theta hcOf hcOf_surj H hcommH) := by
  intro h1 h2 hEq
  have h1' := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2) =>
      LinearMap.GeneralLinearGroup.generalLinearEquiv (GaloisField 2 2)
        (Fin n → GaloisField 2 2) (Matrix.GeneralLinearGroup.toLin g)) hEq
  simp only [w1369_theta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] at h1'
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have hv := congrArg (fun (e : (Fin n → GaloisField 2 2) ≃ₗ[GaloisField 2 2]
      (Fin n → GaloisField 2 2)) => e (Multiplicative.toAdd (ψ w))) h1'
  change w1369_autHom ψ (h1 : MulAut W) (Multiplicative.toAdd (ψ w)) =
    w1369_autHom ψ (h2 : MulAut W) (Multiplicative.toAdd (ψ w)) at hv
  have hψ : ψ ((h1 : MulAut W) w) = ψ ((h2 : MulAut W) w) := by
    apply Multiplicative.toAdd.injective
    simpa only [w1369_autHom_apply, ofAdd_toAdd, ψ.symm_apply_apply] using hv
  exact ψ.injective hψ

private lemma w1369_theta_on_K {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (H : Subgroup (MulAut W))
    (hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W))
    {K : Subgroup (MulAut W)}
    (φ : ↥K ≃* Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2))
    (hact : ∀ (a : ↥K) (w : W), ψ ((a : MulAut W) w) =
      Multiplicative.ofAdd ((φ a : Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec
        (Multiplicative.toAdd (ψ w))))
    (hKH : ∀ k : ↥K, (k : MulAut W) ∈ H) (k : ↥K) :
    w1369_theta hcOf hcOf_surj H hcommH ⟨(k : MulAut W), hKH k⟩ =
      Matrix.SpecialLinearGroup.toGL (φ k) := by
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (GaloisField 2 2)
    (Fin n → GaloisField 2 2)).injective
  apply LinearEquiv.ext
  intro v
  change (w1369_theta hcOf hcOf_surj H hcommH ⟨(k : MulAut W), hKH k⟩ :
      Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec v =
    (φ k : Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec v
  rw [w1369_theta_apply]
  set w : W := ψ.symm (Multiplicative.ofAdd v) with hw
  have hv : Multiplicative.toAdd (ψ w) = v := by
    rw [hw, ψ.apply_symm_apply]
    rfl
  rw [w1369_autHom_apply, hact k w, ← hv]
  rfl

private lemma w1369_theta_equivariance {W : Type} [CommGroup W] {n : ℕ}
    {ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)} {X : Subgroup (MulAut W)}
    {cOf : ↥X → GaloisField 2 2}
    (hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)))
    (hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c)
    (H : Subgroup (MulAut W))
    (hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W))
    (h : ↥H) (w : W) :
    ψ ((h : MulAut W) w) = Multiplicative.ofAdd
      ((w1369_theta hcOf hcOf_surj H hcommH h :
        Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec
          (Multiplicative.toAdd (ψ w))) := by
  rw [w1369_theta_apply, w1369_autHom_apply]
  simp

theorem Std139.concl_of_shapeNat4 (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (h : ShapeNat4 K X n) :
    Concl139 W G X n := by
  classical
  obtain ⟨φ, ψ, hact, hscal⟩ := h
  let H : Subgroup (MulAut W) := G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  have hcommH : ∀ h : ↥H, ∀ x : ↥X,
      (h : MulAut W) * (x : MulAut W) = (x : MulAut W) * (h : MulAut W) := by
    intro h x
    have hC : (h : MulAut W) ∈ Subgroup.centralizer (X : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp h.2).2
    exact (Subgroup.mem_centralizer_iff.mp hC (x : MulAut W) x.2).symm
  let cOf : ↥X → GaloisField 2 2 :=
    fun x => Classical.choose (hscal (x : MulAut W) x.2)
  have hcOf : ∀ x : ↥X, ∀ w : W, ψ ((x : MulAut W) w) =
      Multiplicative.ofAdd (cOf x • Multiplicative.toAdd (ψ w)) :=
    fun x => Classical.choose_spec (hscal (x : MulAut W) x.2)
  have hcOf_inj : Function.Injective cOf := by
    intro x y hxy
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply ψ.injective
    rw [hcOf x w, hcOf y w, hxy]
  have hcOf_ne : ∀ x : ↥X, cOf x ≠ 0 := by
    intro x hx0
    have hconst : ∀ w : W, ψ ((x : MulAut W) w) = 1 := by
      intro w
      rw [hcOf x w, hx0, zero_smul, ofAdd_zero]
    have hconstψ : ∀ w : W, ψ w = 1 := by
      intro w
      obtain ⟨u, rfl⟩ := (x : MulAut W).surjective w
      exact hconst u
    haveI : Subsingleton W := ⟨fun a b => ψ.injective (by rw [hconstψ a, hconstψ b])⟩
    haveI : Subsingleton (MulAut W) :=
      ⟨fun f g => MulEquiv.ext (fun w => Subsingleton.elim _ _)⟩
    have hcard : Nat.card ↥X = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have h3 : Nat.card ↥X = 3 := S.Xcard
    omega
  letI : Fintype ↥X := Fintype.ofFinite _
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcOf_surj : ∀ c : GaloisField 2 2, c ≠ 0 → ∃ x : ↥X, cOf x = c := by
    intro c hc
    have hcardX : Fintype.card ↥X = 3 := by
      rw [← Nat.card_eq_fintype_card, S.Xcard]
    have hcardF : Fintype.card (GaloisField 2 2) = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    have himg_card : (Finset.univ.image cOf).card = 3 := by
      rw [Finset.card_image_of_injective _ hcOf_inj, Finset.card_univ, hcardX]
    have h0 : (0 : GaloisField 2 2) ∉ Finset.univ.image cOf := by
      intro hmem
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmem
      exact hcOf_ne x hx
    have hsub : Finset.univ.image cOf ⊆ Finset.univ.erase (0 : GaloisField 2 2) := by
      intro y hy
      rw [Finset.mem_erase]
      exact ⟨fun hy0 => h0 (hy0 ▸ hy), Finset.mem_univ y⟩
    have herase_card : (Finset.univ.erase (0 : GaloisField 2 2)).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardF]
    have heq : Finset.univ.image cOf = Finset.univ.erase (0 : GaloisField 2 2) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [himg_card, herase_card])
    have hc_mem : c ∈ Finset.univ.erase (0 : GaloisField 2 2) := by
      rw [Finset.mem_erase]
      exact ⟨hc, Finset.mem_univ c⟩
    rw [← heq] at hc_mem
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hc_mem
    exact ⟨x, hx⟩
  have htheta_inj := w1369_theta_injective hcOf hcOf_surj H hcommH
  have hKH : ∀ k : ↥K, (k : MulAut W) ∈ H := by
    intro k
    refine Subgroup.mem_inf.mpr ⟨hK.comp.1 k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Std139.component_commutes_X S hK.comp (k : MulAut W) k.2 x hx).symm
  have hrangeSL : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2) →*
        Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2)).range ≤
      (w1369_theta hcOf hcOf_surj H hcommH).range := by
    rintro g ⟨s, rfl⟩
    obtain ⟨k, rfl⟩ := φ.surjective s
    exact MonoidHom.mem_range.mpr ⟨⟨(k : MulAut W), hKH k⟩,
      w1369_theta_on_K hcOf hcOf_surj H hcommH φ hact hKH k⟩
  let detH : ↥H →* (GaloisField 2 2)ˣ :=
    (Matrix.GeneralLinearGroup.det (n := Fin n) (R := GaloisField 2 2)).comp
      (w1369_theta hcOf hcOf_surj H hcommH)
  haveI : Fact (Nat.card (GaloisField 2 2)ˣ).Prime :=
    ⟨by rw [Nat.card_units, GaloisField.card 2 2 (by norm_num)]; norm_num⟩
  rcases (detH.range).eq_bot_or_eq_top_of_prime_card with hdetbot | hdettop
  · have hdetmem : ∀ h : ↥H, detH h = 1 := by
      intro h
      have hmem : detH h ∈ detH.range := MonoidHom.mem_range.mpr ⟨h, rfl⟩
      rw [hdetbot] at hmem
      simpa using hmem
    let emb : ↥H →* (Matrix.GeneralLinearGroup.det (n := Fin n)
        (R := GaloisField 2 2) : Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2) →*
          (GaloisField 2 2)ˣ).ker :=
      { toFun := fun h => ⟨w1369_theta hcOf hcOf_surj H hcommH h, by
            rw [MonoidHom.mem_ker]
            exact hdetmem h⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp }
    let φSL : ↥H →* Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2) :=
      { toFun := fun h =>
          (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin n) (R := GaloisField 2 2)).symm (emb h)
        map_one' := by simp
        map_mul' := by intro a b; simp }
    have htoGL_φSL : ∀ h : ↥H,
        (Matrix.SpecialLinearGroup.toGL (φSL h) :
          Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2)) =
          w1369_theta hcOf hcOf_surj H hcommH h := by
      intro h
      change Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin n) (R := GaloisField 2 2)).symm
          (emb h)) = _
      rw [← Matrix.SpecialLinearGroup.toGLKerEquiv_apply_coe
        (g := (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin n)
          (R := GaloisField 2 2)).symm (emb h))]
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hφSLinj : Function.Injective φSL := by
      intro a b hab
      apply htheta_inj
      rw [← htoGL_φSL a, ← htoGL_φSL b, hab]
    have hφSLsurj : Function.Surjective φSL := by
      intro s
      obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp (hrangeSL ⟨s, rfl⟩)
      exact ⟨h, Matrix.SpecialLinearGroup.toGL_injective (by rw [htoGL_φSL h, hh])⟩
    refine Or.inr ?_
    let e : ↥H ≃* Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2) :=
      MulEquiv.ofBijective φSL ⟨hφSLinj, hφSLsurj⟩
    refine ⟨e, ψ, fun a w => ?_⟩
    have hmat : (e a : Matrix (Fin n) (Fin n) (GaloisField 2 2)) =
        (w1369_theta hcOf hcOf_surj H hcommH a :
          Matrix (Fin n) (Fin n) (GaloisField 2 2)) := by
      change (φSL a : Matrix (Fin n) (Fin n) (GaloisField 2 2)) = _
      rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix (g := φSL a)]
      exact congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2) =>
        (x : Matrix (Fin n) (Fin n) (GaloisField 2 2))) (htoGL_φSL a)
    rw [hmat]
    exact w1369_theta_equivariance hcOf hcOf_surj H hcommH a w
  · have hsurj : Function.Surjective (w1369_theta hcOf hcOf_surj H hcommH) := by
      intro g
      have hmem : Matrix.GeneralLinearGroup.det (n := Fin n) (R := GaloisField 2 2) g ∈
          detH.range := by rw [hdettop]; exact Subgroup.mem_top _
      obtain ⟨h₀, hh₀⟩ := MonoidHom.mem_range.mp hmem
      have hker : g * (w1369_theta hcOf hcOf_surj H hcommH h₀)⁻¹ ∈
          (Matrix.GeneralLinearGroup.det (n := Fin n) (R := GaloisField 2 2) :
            Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2) →* (GaloisField 2 2)ˣ).ker := by
        rw [MonoidHom.mem_ker]
        show Matrix.GeneralLinearGroup.det (g * (w1369_theta hcOf hcOf_surj H hcommH h₀)⁻¹) = 1
        rw [map_mul, map_inv]
        have hΘdet : Matrix.GeneralLinearGroup.det (n := Fin n) (R := GaloisField 2 2)
            (w1369_theta hcOf hcOf_surj H hcommH h₀) = detH h₀ := rfl
        rw [hΘdet, ← hh₀, mul_inv_cancel]
      have hmem2 : g * (w1369_theta hcOf hcOf_surj H hcommH h₀)⁻¹ ∈
          (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2) →*
              Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2)).range := by
        rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
        exact hker
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hmem2
      obtain ⟨h₁, hh₁⟩ := MonoidHom.mem_range.mp (hrangeSL ⟨s, hs⟩)
      exact ⟨h₁ * h₀, by rw [map_mul, hh₁]; group⟩
    refine Or.inl (Or.inl ?_)
    let e : ↥H ≃* Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2) :=
      MulEquiv.ofBijective (w1369_theta hcOf hcOf_surj H hcommH) ⟨htheta_inj, hsurj⟩
    refine ⟨e, ψ, fun a w => ?_⟩
    exact w1369_theta_equivariance hcOf hcOf_surj H hcommH a w


end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
