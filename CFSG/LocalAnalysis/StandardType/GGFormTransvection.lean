module

public import CFSG.ClassicalGroups.Linear.CentreTransvections
public import CFSG.ClassicalGroups.Linear.TwoCentres
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianBasic

public section

namespace CFSG.StandardType

lemma exists_anisotropic_of_hermitian {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] (τ : F ≃+* F) (hτ : ∃ c, τ c ≠ c) (H : V → V → F)
    (hherm : ∀ x y, H x y = τ (H y x))
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0) :
    ∃ v, H v v ≠ 0 := by
  let h : V →ₛₗ[(τ : F →+* F)] V →ₗ[F] F :=
    LinearMap.mk₂'ₛₗ (τ : F →+* F) (RingHom.id F) H haddL hsmulL haddR hsmulR
  have hne : τ ≠ 1 := by
    obtain ⟨c, hc⟩ := hτ
    intro h1
    exact hc (by rw [h1]; rfl)
  have hnd' : h.Nondegenerate := by
    refine ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => ?_⟩
    rw [hherm y x]
    have h0 : H x y = 0 := hy x
    rw [h0, map_zero]
  exact CFSG.ComponentClassification.CatalogueBHermitian.exists_self_ne_zero h hnd' hne

private lemma ftv_exists_dual_eq_zero_ne {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hk : 2 ≤ Module.finrank F V) (v : V) :
    ∃ φ : Module.Dual F V, φ v = 0 ∧ φ ≠ 0 := by
  let b : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  let φ₀ : Module.Dual F V := b.coord ⟨0, by omega⟩
  let φ₁ : Module.Dual F V := b.coord ⟨1, by omega⟩
  by_cases hq : φ₁ v = 0
  · refine ⟨φ₁, hq, ?_⟩
    intro h0
    have h := congrArg (fun f : Module.Dual F V => f (b ⟨1, by omega⟩)) h0
    simp only [LinearMap.zero_apply] at h
    have h1 : (φ₁ : V → F) (b ⟨1, by omega⟩) = 1 := by
      simp [φ₁, Module.Basis.coord_apply]
    rw [h1] at h
    exact one_ne_zero h
  · refine ⟨(φ₁ v) • φ₀ - (φ₀ v) • φ₁, ?_, ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · intro h0
      have h := congrArg (fun f : Module.Dual F V => f (b ⟨0, by omega⟩)) h0
      simp only [LinearMap.zero_apply] at h
      have h1 : ((φ₁ v) • φ₀ - (φ₀ v) • φ₁ : Module.Dual F V) (b ⟨0, by omega⟩) =
          φ₁ v := by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        have hφ₀ : (φ₀ : V → F) (b ⟨0, by omega⟩) = 1 := by
          simp [φ₀, Module.Basis.coord_apply]
        have hφ₁ : (φ₁ : V → F) (b ⟨0, by omega⟩) = 0 := by
          simp [φ₁, Module.Basis.coord_apply]
        rw [hφ₀, hφ₁]
        ring
      rw [h1] at h
      exact hq h

private lemma ftv_not_isometry_of_dual {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V]
    (H : V → V → F) (v : V) (φ : Module.Dual F V)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hφv : φ v = 0) (hφ0 : φ ≠ 0) (hv : H v v ≠ 0) :
    ¬ (∀ x y, H (ClassicalGroups.Linear.transv v φ x)
      (ClassicalGroups.Linear.transv v φ y) = H x y) := by
  intro hiso
  apply hφ0
  ext y
  have h1 := hiso v y
  rw [ClassicalGroups.Linear.transv_apply, ClassicalGroups.Linear.transv_apply, hφv,
    zero_smul, add_zero, haddR, hsmulR] at h1
  exact (mul_eq_zero.mp (add_left_cancel (by rw [add_zero]; exact h1))).resolve_right hv

lemma exists_transvection_not_isometry {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : V → V → F) (hk : 2 ≤ Module.finrank F V)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (haniso : ∃ v, H v v ≠ 0) :
    ∃ t : V ≃ₗ[F] V, LinearMap.det (t : V →ₗ[F] V) = 1 ∧
      ¬ (∀ x y, H (t x) (t y) = H x y) := by
  obtain ⟨v, hv⟩ := haniso
  obtain ⟨φ, hφv, hφ0⟩ := ftv_exists_dual_eq_zero_ne hk v
  refine ⟨LinearEquiv.ofLinearMap (ClassicalGroups.Linear.transv v φ)
    (ClassicalGroups.Linear.transv v (-φ)) ?_ ?_, ?_, ?_⟩
  · exact LinearMap.ext fun x => ClassicalGroups.Linear.transv_transv_neg_apply hφv x
  · exact LinearMap.ext fun x => ClassicalGroups.Linear.transv_neg_transv_apply hφv x
  · exact ClassicalGroups.Linear.det_id_add_smulRight (Module.finBasis F V) hφv
  · exact ftv_not_isometry_of_dual H v φ haddR hsmulR hφv hφ0 hv

private lemma ftv_neg_eq_self {F : Type*} [Field F] [CharP F 2] (x : F) : -x = x := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [neg_eq_iff_add_eq_zero]
  calc x + x = (2 : F) * x := by ring
    _ = 0 := by rw [htwo, zero_mul]

private lemma ftv_form_sub_second {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (H : V → V → F) (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y) (x y z : V) :
    H x (y - z) = H x y - H x z := by
  rw [sub_eq_add_neg, haddR, show -z = (-1 : F) • z from (neg_one_smul F z).symm, hsmulR]
  ring

private lemma ftv_alt_comm {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V]
    (H : V → V → F) (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (halt : ∀ v, H v v = 0) (x y : V) : H x y = H y x := by
  have h0 : H (x + y) (x + y) = 0 := halt (x + y)
  rw [haddL, haddR, haddR, halt x, halt y] at h0
  have h1 : H y x = -H x y := by linear_combination h0
  rw [ftv_neg_eq_self] at h1
  exact h1.symm

private lemma ftv_exists_alt_pair {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V]
    (H : V → V → F) (hsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0) (x : V) (hx : x ≠ 0) :
    ∃ a b : V, H a b = 1 := by
  have hw : ∃ w, H x w ≠ 0 := not_forall.mp (fun h => hx (hnd x h))
  obtain ⟨w, hw⟩ := hw
  exact ⟨x, (H x w)⁻¹ • w, by rw [hsmulR, inv_mul_cancel₀ hw]⟩

private lemma ftv_alt_not_isometry {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V]
    (H : V → V → F) (a b : V) (φ : Module.Dual F V)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : F) x y, H x (c • y) = c * H x y)
    (hφb : φ b = 0) (hba : H b a = 1) (hφ0 : φ ≠ 0) :
    ¬ (∀ x y, H (ClassicalGroups.Linear.transv a φ x)
      (ClassicalGroups.Linear.transv a φ y) = H x y) := by
  intro hiso
  apply hφ0
  ext y
  have h1 := hiso b y
  simp only [ClassicalGroups.Linear.transv_apply, hφb, zero_smul, add_zero,
    zero_mul, zero_add, haddR, hsmulR, hba, mul_one] at h1
  have h2 : φ y = 0 :=
    add_left_cancel (show H b y + φ y = H b y + 0 by rw [add_zero]; exact h1)
  simpa using h2

lemma exists_transvection_not_isometry_of_alternating {F V : Type*} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : V → V → F) (hk : 3 ≤ Module.finrank F V)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (halt : ∀ v, H v v = 0)
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0) :
    ∃ t : V ≃ₗ[F] V, LinearMap.det (t : V →ₗ[F] V) = 1 ∧
      ¬ (∀ x y, H (t x) (t y) = H x y) := by
  let B : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  let i0 : Fin (Module.finrank F V) := ⟨0, by omega⟩
  have hB0 : B i0 ≠ 0 := B.ne_zero i0
  obtain ⟨a, b, hab⟩ := ftv_exists_alt_pair H hsmulR hnd (B i0) hB0
  have hba : H b a = 1 := by
    rw [ftv_alt_comm H haddL haddR halt b a, hab]
  have hp2 : Module.finrank F (Submodule.span F ({a, b} : Set V)) ≤ 2 := by
    have h := finrank_range_le_card (R := F) ![a, b]
    rw [Set.finrank, Fintype.card_fin] at h
    have hrange : Set.range ![a, b] = ({a, b} : Set V) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rwa [hrange] at h
  have hpne : Submodule.span F ({a, b} : Set V) ≠ ⊤ := by
    intro htop
    have hk' : Module.finrank F (Submodule.span F ({a, b} : Set V)) = Module.finrank F V := by
      rw [htop, finrank_top]
    omega
  obtain ⟨z, hz⟩ : ∃ z, z ∉ Submodule.span F ({a, b} : Set V) := by
    by_contra h
    push Not at h
    exact hpne (le_antisymm le_top fun x _ => h x)
  let w : V := z - H a z • b - H b z • a
  have hwa : H a w = 0 := by
    change H a (z - H a z • b - H b z • a) = 0
    rw [ftv_form_sub_second H haddR hsmulR, ftv_form_sub_second H haddR hsmulR,
      hsmulR, hsmulR, hab, mul_one, halt a, mul_zero]
    ring
  have hwb : H b w = 0 := by
    change H b (z - H a z • b - H b z • a) = 0
    rw [ftv_form_sub_second H haddR hsmulR, ftv_form_sub_second H haddR hsmulR,
      hsmulR, hsmulR, halt b, mul_zero, hba, mul_one]
    ring
  have hw0 : w ≠ 0 := by
    intro hw
    apply hz
    change z - H a z • b - H b z • a = 0 at hw
    have h1 : z - H a z • b = H b z • a := sub_eq_zero.mp hw
    have h2 : z = H a z • b + H b z • a := by
      rw [← h1]; abel
    rw [h2]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  let φ : Module.Dual F V :=
    { toFun := fun y => H w y
      map_add' := fun y y' => haddR w y y'
      map_smul' := fun c y => by rw [hsmulR, smul_eq_mul, RingHom.id_apply] }
  have hφa : φ a = 0 := by
    change H w a = 0
    rw [ftv_alt_comm H haddL haddR halt w a, hwa]
  have hφb : φ b = 0 := by
    change H w b = 0
    rw [ftv_alt_comm H haddL haddR halt w b, hwb]
  have hφ0 : φ ≠ 0 := by
    intro hzero
    apply hw0
    apply hnd w
    intro y
    have := congrArg (fun f : Module.Dual F V => f y) hzero
    exact this
  have hnot := ftv_alt_not_isometry H a b φ haddR hsmulR hφb hba hφ0
  refine ⟨LinearEquiv.ofLinearMap (ClassicalGroups.Linear.transv a φ)
    (ClassicalGroups.Linear.transv a (-φ)) ?_ ?_, ?_, hnot⟩
  · exact LinearMap.ext fun x => ClassicalGroups.Linear.transv_transv_neg_apply hφa x
  · exact LinearMap.ext fun x => ClassicalGroups.Linear.transv_neg_transv_apply hφa x
  · exact ClassicalGroups.Linear.det_id_add_smulRight (Module.finBasis F V) hφa

end CFSG.StandardType
