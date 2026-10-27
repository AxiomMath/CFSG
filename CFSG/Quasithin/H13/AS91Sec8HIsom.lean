module

public import CFSG.Quasithin.H13.AS91Sec8HPi
public import CFSG.Quasithin.Background.HatM22Commutant
public import CFSG.LinearAlgebra.InvariantQuadraticFormUnique

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin.HatM22
open CFSG.CharacterTheory.SteinbergBY (FieldFour)
open CFSG.CharacterTheory.SteinbergBY.FieldFour (ω ω₂ ω_ne_zero ω_ne_one ω₂_ne_zero ω_sq)

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}

abbrev toSMN (c : Loc41 G z) (n : ↥c.NX) : ↥c.S.M :=
  ⟨(n : G), c.SM_eq.symm ▸ n.2.1⟩

@[simp]
theorem coe_toSMN (c : Loc41 G z) (n : ↥c.NX) : ((c.toSMN n : c.S.M) : G) = (n : G) := rfl

@[simp]
theorem toSMN_mul (c : Loc41 G z) (m n : ↥c.NX) :
    c.toSMN (m * n) = c.toSMN m * c.toSMN n := rfl

@[simp]
theorem toSMN_one (c : Loc41 G z) : c.toSMN 1 = 1 := rfl

@[simp]
theorem toSMN_inv (c : Loc41 G z) (n : ↥c.NX) : c.toSMN n⁻¹ = (c.toSMN n)⁻¹ := rfl

theorem toSMN_of_mem_CX (c : Loc41 G z) (h : ↥c.CX) :
    c.toSMN ⟨h, c.CX_le_NX h.2⟩ = c.toSM h := rfl

@[simp]
theorem toSM_mul (c : Loc41 G z) (h k : ↥c.CX) :
    c.toSM (h * k) = c.toSM h * c.toSM k := rfl

@[simp]
theorem toSM_one (c : Loc41 G z) : c.toSM 1 = 1 := rfl

@[simp]
theorem toSM_inv (c : Loc41 G z) (h : ↥c.CX) : c.toSM h⁻¹ = (c.toSM h)⁻¹ := rfl

@[simp]
theorem toSM_pow (c : Loc41 G z) (h : ↥c.CX) (n : ℕ) :
    c.toSM (h ^ n) = c.toSM h ^ n := rfl

end Loc41

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def ψLin (c : Loc41 G z) :
    c.S.Qt ≃ₗ[ZMod 2] (Fin 6 → FieldFour) :=
  c.ψ.toLinearEquiv fun a v => by
    rcases CFSG.Quasithin.H13.J4.zmod2_cases a with rfl | rfl <;> simp

@[simp]
theorem ψLin_apply (c : Loc41 G z) (v : c.S.Qt) : c.ψLin v = c.ψ v := rfl

@[simp]
theorem ψLin_symm_apply (c : Loc41 G z) (w : Fin 6 → FieldFour) :
    c.ψLin.symm w = c.ψ.symm w := rfl

@[expose] noncomputable def muLin (c : Loc41 G z) (e : FieldFour) :
    c.S.Qt →ₗ[ZMod 2] c.S.Qt where
  toFun v := c.ψ.symm (e • c.ψ v)
  map_add' v w := by
    simp only [map_add, smul_add]
  map_smul' a v := by
    show c.ψ.symm (e • c.ψ (a • v)) = a • c.ψ.symm (e • c.ψ v)
    rw [show c.ψ (a • v) = a • c.ψ v from c.ψLin.map_smul a v, smul_comm e a]
    exact c.ψLin.symm.map_smul a (e • c.ψ v)

@[simp]
theorem muLin_apply (c : Loc41 G z) (e : FieldFour) (v : c.S.Qt) :
    c.muLin e v = c.ψ.symm (e • c.ψ v) := rfl

theorem muLin_leftInverse (c : Loc41 G z) (e : FieldFour) (he : e ≠ 0) :
    Function.LeftInverse (c.muLin e⁻¹) (c.muLin e) := by
  intro v
  rw [muLin_apply, muLin_apply, AddEquiv.apply_symm_apply, smul_smul,
    inv_mul_cancel₀ he, one_smul, AddEquiv.symm_apply_apply]

theorem muLin_bijective (c : Loc41 G z) (e : FieldFour) (he : e ≠ 0) :
    Function.Bijective (c.muLin e) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨c.muLin e⁻¹, c.muLin_leftInverse e he, ?_⟩
  intro v
  rw [muLin_apply, muLin_apply, AddEquiv.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ he, one_smul, AddEquiv.symm_apply_apply]

@[expose] noncomputable def muEquiv (c : Loc41 G z) (e : FieldFour) (he : e ≠ 0) :
    c.S.Qt ≃ₗ[ZMod 2] c.S.Qt :=
  LinearEquiv.ofBijective (c.muLin e) (c.muLin_bijective e he)

@[simp]
theorem muEquiv_apply (c : Loc41 G z) (e : FieldFour) (he : e ≠ 0) (v : c.S.Qt) :
    c.muEquiv e he v = c.ψ.symm (e • c.ψ v) := by
  rw [muEquiv, LinearEquiv.ofBijective_apply, muLin_apply]

theorem muEquiv_apply_ψ (c : Loc41 G z) (e : FieldFour) (he : e ≠ 0) (v : c.S.Qt) :
    c.ψ (c.muEquiv e he v) = e • c.ψ v := by
  rw [muEquiv_apply, AddEquiv.apply_symm_apply]

end Loc41

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}
variable {G' : Type} [Group G'] [Finite G'] {z' : G'}

@[expose] noncomputable def baseEquiv (c : Loc41 G z) (c' : Loc41 G' z') :
    c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt :=
  c.ψLin.trans c'.ψLin.symm

@[simp]
theorem baseEquiv_apply (c : Loc41 G z) (c' : Loc41 G' z') (v : c.S.Qt) :
    c.baseEquiv c' v = c'.ψ.symm (c.ψ v) := rfl

@[simp]
theorem ψ_baseEquiv (c : Loc41 G z) (c' : Loc41 G' z') (v : c.S.Qt) :
    c'.ψ (c.baseEquiv c' v) = c.ψ v := by
  rw [baseEquiv_apply, AddEquiv.apply_symm_apply]

theorem semilinear_mu (c : Loc41 G z) (A : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)
    (hsemi : ∀ (e : FieldFour) (v : c.S.Qt),
      c.ψ (A (c.ψ.symm (e • c.ψ v))) = (e * e) • c.ψ (A v))
    (e : FieldFour) (he : e ≠ 0) (v : c.S.Qt) :
    A (c.muEquiv e he v) = c.muEquiv (e * e) (mul_ne_zero he he) (A v) := by
  apply c.ψLin.injective
  change c.ψ (A (c.muEquiv e he v)) = c.ψ (c.muEquiv (e * e) _ (A v))
  rw [c.muEquiv_apply, hsemi, c.muEquiv_apply_ψ]

theorem baseEquiv_equivariant (c : Loc41 G z) (c' : Loc41 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (h : ↥c.CX) (v : c.S.Qt) :
    c.baseEquiv c' ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
      (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (c.baseEquiv c' v) := by
  apply c'.ψLin.injective
  change c'.ψ (c.baseEquiv c' ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v)) =
    c'.ψ ((c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (c.baseEquiv c' v))
  rw [ψ_baseEquiv, c.piC_spec, c'.piC_spec, hθ, ψ_baseEquiv]

theorem baseEquiv_symm_equivariant (c : Loc41 G z) (c' : Loc41 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (h : ↥c.CX) (v : c'.S.Qt) :
    (c.baseEquiv c').symm ((c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v) =
      (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) ((c.baseEquiv c').symm v) := by
  apply (c.baseEquiv c').injective
  rw [LinearEquiv.apply_symm_apply,
    baseEquiv_equivariant c c' θ hθ h ((c.baseEquiv c').symm v),
    LinearEquiv.apply_symm_apply]

end Loc41

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_x0_piC_hatM22Z
    (c : Loc49 G z) :
    ∃ x : ↥c.X, (x : G) ≠ 1 ∧ c.piC ⟨x, c.X_le_CX x.2⟩ = hatM22Z := by
  have hnt : Nontrivial ↥c.X := by
    rw [← Finite.one_lt_card_iff_nontrivial, c.card_X]
    norm_num
  obtain ⟨x₁, hx₁⟩ := exists_ne (1 : ↥c.X)
  have hx₁' : (x₁ : G) ≠ 1 := fun h => hx₁ (Subtype.ext h)
  rcases c.piC_of_mem_X x₁.2 hx₁' with hZ | hZ2
  · exact ⟨x₁, hx₁', hZ⟩
  · refine ⟨x₁ ^ 2, ?_, ?_⟩
    · intro h
      have h2 : (x₁ : G) * (x₁ : G) = 1 := by
        have h' : (x₁ : G) ^ 2 = 1 := by simpa using h
        simpa [pow_two] using h'
      have hdvd3 : orderOf (x₁ : G) ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard c.X x₁.2
        rwa [c.card_X] at this
      have hdvd2 : orderOf (x₁ : G) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]
        exact h2
      have hone : orderOf (x₁ : G) = 1 := by
        have hdvd : orderOf (x₁ : G) ∣ Nat.gcd 3 2 := Nat.dvd_gcd hdvd3 hdvd2
        simpa using hdvd
      exact hx₁ (Subtype.ext (orderOf_eq_one_iff.mp hone))
    · have hx1sq : (⟨x₁ ^ 2, c.X_le_CX (x₁ ^ 2).2⟩ : ↥c.CX) =
          (⟨x₁, c.X_le_CX x₁.2⟩ : ↥c.CX) ^ 2 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
      change c.piC (⟨x₁ ^ 2, c.X_le_CX (x₁ ^ 2).2⟩ : ↥c.CX) = hatM22Z
      rw [hx1sq, map_pow, hZ2]
      have h4 : (hatM22Z ^ 2) ^ 2 = hatM22Z := by
        have h3 : hatM22Z ^ 3 = 1 := hatM22Z_pow_three
        calc (hatM22Z ^ 2) ^ 2 = hatM22Z ^ (2 * 2) := by rw [← pow_mul]
          _ = hatM22Z ^ (3 + 1) := by rw [show (2 * 2 : ℕ) = 3 + 1 by norm_num]
          _ = hatM22Z ^ 3 * hatM22Z := by rw [pow_add, pow_one]
          _ = 1 * hatM22Z := by rw [h3]
          _ = hatM22Z := by rw [one_mul]
      exact h4

@[expose] noncomputable def wEquiv (c : Loc49 G z) (x : ↥c.X) :
    c.S.Qt ≃ₗ[ZMod 2] c.S.Qt :=
  ((c.S.ρ (c.toSM ⟨x, c.X_le_CX x.2⟩) : c.S.O) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)

@[simp]
theorem wEquiv_apply (c : Loc49 G z) (x : ↥c.X) (v : c.S.Qt) :
    c.wEquiv x v =
      ((c.S.ρ (c.toSM ⟨x, c.X_le_CX x.2⟩) : c.S.O) :
        c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v := rfl

theorem wEquiv_eq_mu (c : Loc49 G z) (x : ↥c.X)
    (hx : c.piC ⟨x, c.X_le_CX x.2⟩ = hatM22Z) :
    c.wEquiv x = c.muEquiv ω ω_ne_zero := by
  apply LinearEquiv.ext
  intro v
  apply c.ψLin.injective
  change c.ψ (c.wEquiv x v) = c.ψ (c.muEquiv ω ω_ne_zero v)
  rw [c.wEquiv_apply, c.piC_spec, hx, hatM22Z_val, Matrix.smul_mulVec,
    Matrix.one_mulVec, c.muEquiv_apply_ψ]

theorem wEquiv_apply_wEquiv (c : Loc49 G z) (x : ↥c.X)
    (hx : c.piC ⟨x, c.X_le_CX x.2⟩ = hatM22Z) (v : c.S.Qt) :
    c.wEquiv x (c.wEquiv x v) = c.muEquiv ω₂ ω₂_ne_zero v := by
  rw [wEquiv_eq_mu c x hx]
  apply c.ψLin.injective
  change c.ψ (c.muEquiv ω ω_ne_zero (c.muEquiv ω ω_ne_zero v)) =
    c.ψ (c.muEquiv ω₂ ω₂_ne_zero v)
  rw [c.muEquiv_apply_ψ, c.muEquiv_apply_ψ, c.muEquiv_apply_ψ, smul_smul, ← pow_two, ω_sq]

theorem wEquiv_add (c : Loc49 G z) (x : ↥c.X)
    (hx : c.piC ⟨x, c.X_le_CX x.2⟩ = hatM22Z) (v : c.S.Qt) :
    c.wEquiv x (c.wEquiv x v) + c.wEquiv x v + v = 0 := by
  apply c.ψLin.injective
  change c.ψ (c.wEquiv x (c.wEquiv x v) + c.wEquiv x v + v) = c.ψ 0
  rw [map_add, map_add, wEquiv_apply_wEquiv c x hx, wEquiv_eq_mu c x hx,
    c.muEquiv_apply_ψ, c.muEquiv_apply_ψ, map_zero]
  have hω : ω₂ + ω + 1 = 0 := by decide
  have h : ω₂ • c.ψ v + ω • c.ψ v + c.ψ v = (ω₂ + ω + 1) • c.ψ v := by
    rw [add_smul, add_smul, one_smul]
  rw [h, hω, zero_smul]

@[expose] noncomputable def rhoNX (c : Loc49 G z) (n : ↥c.NX) :
    c.S.Qt ≃ₗ[ZMod 2] c.S.Qt :=
  (c.S.ρ (c.toSMN n) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)

@[simp]
theorem rhoNX_apply (c : Loc49 G z) (n : ↥c.NX) (v : c.S.Qt) :
    c.rhoNX n v = (c.S.ρ (c.toSMN n) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v := rfl

@[simp]
theorem rhoNX_mul (c : Loc49 G z) (m n : ↥c.NX) :
    c.rhoNX (m * n) = c.rhoNX m * c.rhoNX n := by
  rw [rhoNX, rhoNX, rhoNX, c.toSMN_mul, map_mul, Subgroup.coe_mul]

@[simp]
theorem rhoNX_one (c : Loc49 G z) : c.rhoNX 1 = 1 := by
  rw [rhoNX, c.toSMN_one, map_one]; rfl

@[simp]
theorem rhoNX_inv (c : Loc49 G z) (n : ↥c.NX) :
    c.rhoNX n⁻¹ = (c.rhoNX n)⁻¹ := by
  rw [rhoNX, rhoNX, c.toSMN_inv, map_inv, Subgroup.coe_inv]

theorem rhoNX_of_mem_CX (c : Loc49 G z) (h : ↥c.CX) :
    c.rhoNX ⟨h, c.CX_le_NX h.2⟩ =
      (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) := rfl

theorem muEquiv_commute_rho_CX (c : Loc49 G z) (h : ↥c.CX) (e : FieldFour) (he : e ≠ 0) :
    c.muEquiv e he * (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) =
      (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) * c.muEquiv e he := by
  apply LinearEquiv.ext
  intro v
  apply c.ψLin.injective
  change c.ψ (c.muEquiv e he ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v)) =
    c.ψ ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (c.muEquiv e he v))
  rw [c.muEquiv_apply_ψ, c.piC_spec, c.piC_spec, c.muEquiv_apply_ψ, Matrix.mulVec_smul]

theorem exists_muLin_of_commute_CX (c : Loc49 G z)
    (L : c.S.Qt →ₗ[ZMod 2] c.S.Qt)
    (hL : ∀ h : ↥c.CX, ∀ v,
      L ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
        (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (L v)) :
    ∃ e : FieldFour, L = c.muLin e := by
  let φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour) :=
    { toFun := fun x => c.ψ (L (c.ψ.symm x))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [map_add, L.map_add] }
  have hφ_apply : ∀ x, φ x = c.ψ (L (c.ψ.symm x)) := fun _ => rfl
  have hφ : ∀ γ ∈ hatM22Γ₀, ∀ v : Fin 6 → FieldFour,
      φ (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (φ v) := by
    intro γ hγ v
    obtain ⟨h, hh⟩ := c.piC_surjective ⟨γ, hγ⟩
    have hγeq : γ = (((c.piC h : ↥hatM22Γ₀) :
        Matrix.GeneralLinearGroup (Fin 6) FieldFour)) := by rw [hh]
    rw [hγeq]
    have hsymm : c.ψ.symm ((((c.piC h : ↥hatM22Γ₀) :
        Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
        (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (c.ψ.symm v) := by
      rw [show (((c.piC h : ↥hatM22Γ₀) :
          Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
            Matrix (Fin 6) (Fin 6) FieldFour).mulVec v =
          c.ψ ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (c.ψ.symm v)) by
        rw [c.piC_spec, AddEquiv.apply_symm_apply]]
      rw [AddEquiv.symm_apply_apply]
    simp only [hφ_apply, hsymm, hL h (c.ψ.symm v), c.piC_spec, AddEquiv.apply_symm_apply]
  obtain ⟨e, he⟩ := exists_eq_smul_of_commute_hatM22Γ₀ φ hφ
  refine ⟨e, ?_⟩
  apply LinearMap.ext
  intro v
  apply c.ψLin.injective
  change c.ψ (L v) = c.ψ (c.muLin e v)
  have hv : c.ψ (L v) = φ (c.ψ v) := by
    show c.ψ (L v) = c.ψ (L (c.ψ.symm (c.ψ v)))
    rw [AddEquiv.symm_apply_apply]
  rw [hv, he (c.ψ v), c.muLin_apply, AddEquiv.apply_symm_apply]

end Loc49

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}
variable {G' : Type} [Group G'] [Finite G'] {z' : G'}

theorem not_linear_toSMN
    (c : Loc49 G z) (c' : Loc49 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (θN : ↥c.NX ≃* ↥c'.NX)
    (hext : ∀ h : ↥c.CX, ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = (θ h : G'))
    (t : ↥c.NX) (htinv : ∀ x ∈ c.X, (t : G) * x * (t : G)⁻¹ = x⁻¹)
    (x0 : ↥c.X) (hx0Z : c.piC ⟨x0, c.X_le_CX x0.2⟩ = hatM22Z) :
    ¬ ∃ γ ∈ hatM22Γ₀, ∀ v : c'.S.Qt,
      c'.ψ ((c'.S.ρ (c'.toSMN (θN t)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v) =
        (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (c'.ψ v)) := by
  rintro ⟨γ, hγ, hγlin⟩
  let x0CX : ↥c.CX := ⟨x0, c.X_le_CX x0.2⟩
  let x0NX : ↥c.NX := ⟨x0, c.X_le_NX x0.2⟩
  let x0' : ↥c'.CX := θ x0CX
  let x0NX' : ↥c'.NX := ⟨x0', c'.CX_le_NX x0'.2⟩
  let t' : ↥c'.NX := θN t
  let A : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt :=
    (c'.S.ρ (c'.toSMN t') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)
  let B : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt :=
    (c'.S.ρ (c'.toSM x0') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)
  let M : Matrix (Fin 6) (Fin 6) FieldFour :=
    (((hatM22Z : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
      Matrix (Fin 6) (Fin 6) FieldFour)
  have hx0'_eq : θN x0NX = x0NX' := by
    apply Subtype.ext
    exact hext x0CX
  have ht_inv_x0 : t * x0NX * t⁻¹ = x0NX⁻¹ := by
    apply Subtype.ext
    simpa [x0NX] using htinv (x0 : G) x0.2
  have ht'_inv : t' * x0NX' * t'⁻¹ = x0NX'⁻¹ := by
    rw [← hx0'_eq]
    calc t' * θN x0NX * t'⁻¹ = θN (t * x0NX * t⁻¹) := by
          simp [t', map_mul, map_inv]
      _ = θN (x0NX⁻¹) := by rw [ht_inv_x0]
      _ = (θN x0NX)⁻¹ := map_inv θN x0NX
  have hA_B_inv : A * B * A⁻¹ = B⁻¹ := by
    have h := congrArg (fun n : ↥c'.NX =>
      (c'.S.ρ (c'.toSMN n) : c'.S.O)) ht'_inv
    have h1 : c'.toSMN (t' * x0NX' * t'⁻¹) =
        c'.toSMN t' * c'.toSM x0' * (c'.toSMN t')⁻¹ := by
      rw [c'.toSMN_mul, c'.toSMN_mul, c'.toSMN_inv, c'.toSMN_of_mem_CX]
    rw [h1, map_mul, map_mul, map_inv] at h
    simpa [A, B] using congrArg (fun x : c'.S.O =>
      (x : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)) h
  have hB_piC : c'.piC x0' = hatM22Z := by
    rw [show x0' = θ x0CX from rfl, hθ x0CX, hx0Z]
  have hB_spec : ∀ v, c'.ψ (B v) = M.mulVec (c'.ψ v) := by
    intro v
    rw [show B = (c'.S.ρ (c'.toSM x0') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) from rfl]
    rw [c'.piC_spec x0' v, hB_piC]
  have hx0_central_CX : x0CX ∈ Subgroup.center ↥c.CX := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : (y : G) ∈ centralizer (c.X : Set G) := y.2.2
    have hxy : (x0 : G) * (y : G) = (y : G) * (x0 : G) :=
      Subgroup.mem_centralizer_iff.mp hy (x0 : G) x0.2
    simpa [x0CX] using hxy.symm
  have hcentral : x0' ∈ Subgroup.center ↥c'.CX := by
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y, rfl⟩ := θ.surjective y'
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subgroup.mem_center_iff.mp hx0_central_CX y)
  obtain ⟨h, hh⟩ := c'.piC_surjective ⟨γ, hγ⟩
  have hA_eq : A = (c'.S.ρ (c'.toSM h) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) := by
    apply LinearEquiv.ext
    intro v
    apply c'.ψLin.injective
    change c'.ψ (A v) = c'.ψ ((c'.S.ρ (c'.toSM h) :
      c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v)
    rw [hγlin v, c'.piC_spec h v, hh]
  have hAB : A * B = B * A := by
    have hcomm := Subgroup.mem_center_iff.mp hcentral h
    have h2 : c'.toSM (h * x0') = c'.toSM h * c'.toSM x0' := c'.toSM_mul h x0'
    have h3 : c'.toSM (x0' * h) = c'.toSM x0' * c'.toSM h := c'.toSM_mul x0' h
    have h4 := congrArg (fun y : ↥c'.CX =>
      (c'.S.ρ (c'.toSM y) : c'.S.O)) hcomm
    rw [h2, h3, map_mul, map_mul] at h4
    have h5 := congrArg (fun x : c'.S.O =>
      (x : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)) h4
    simpa [A, B, hA_eq] using h5
  have hB_inv : B = B⁻¹ := by
    rw [← hA_B_inv, hAB]
    group
  have hB2 : B * B = 1 := by
    nth_rewrite 1 [hB_inv]
    exact inv_mul_cancel B
  have hx03 : x0 ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := x0)
    rwa [c.card_X] at h
  have hx0CX3 : x0CX ^ 3 = 1 := by
    apply Subtype.ext
    have h := congrArg Subtype.val hx03
    simpa [x0CX, Subgroup.coe_pow] using h
  have hx0'3 : x0' ^ 3 = 1 := by
    calc x0' ^ 3 = (θ x0CX) ^ 3 := rfl
      _ = θ (x0CX ^ 3) := (map_pow θ x0CX 3).symm
      _ = 1 := by rw [hx0CX3, map_one]
  have hB3 : B ^ 3 = 1 := by
    have h : (c'.S.ρ (c'.toSM x0') : c'.S.O) ^ 3 =
        c'.S.ρ (c'.toSM (x0' ^ 3)) := by
      rw [← map_pow, c'.toSM_pow]
    have h' : B ^ 3 = ((c'.S.ρ (c'.toSM (x0' ^ 3)) : c'.S.O) :
        c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) := by
      rw [show B = ((c'.S.ρ (c'.toSM x0') : c'.S.O) :
          c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) from rfl]
      rw [← Subgroup.coe_pow, h]
    rw [h', hx0'3]
    simp
  have hB1 : B = 1 := by
    calc B = B ^ 3 * (B ^ 2)⁻¹ := by group
      _ = 1 := by rw [hB3, pow_two, hB2, inv_one, mul_one]
  have hM1 : M = 1 := by
    apply c'.eq_of_mulVec_ψ_eq
    intro v
    have h1 : c'.ψ (B v) = c'.ψ v := by rw [hB1]; rfl
    have h2 : M.mulVec (c'.ψ v) = c'.ψ v := by
      rw [← hB_spec v, h1]
    rw [h2, Matrix.one_mulVec]
  have hZ1 : (hatM22Z : ↥hatM22Γ₀) = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hM1
  have hω1 : ω = 1 := by
    have h := congrArg (fun x : ↥hatM22Γ₀ =>
      ((((x : Matrix.GeneralLinearGroup (Fin 6) FieldFour)) :
        Matrix (Fin 6) (Fin 6) FieldFour) 0 0)) hZ1
    simpa [hatM22Z_val] using h
  exact ω_ne_one hω1

end Loc49

@[expose] def IsEquivariantNX {G : Type} [Group G] [Finite G] {z : G}
    {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z')
    (a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (θN : ↥c.NX ≃* ↥c'.NX) (n : ↥c.NX) : Prop :=
  ∀ v, a ((c.S.ρ (c.toSMN n) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
    (c'.S.ρ (c'.toSMN (θN n)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}
variable {G' : Type} [Group G'] [Finite G'] {z' : G'}

@[expose] noncomputable def Psub {G : Type} [Group G] [Finite G] {z : G}
    {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z')
    (a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (θN : ↥c.NX ≃* ↥c'.NX) :
    Subgroup ↥c.NX where
  carrier := {n | IsEquivariantNX c c' a θN n}
  one_mem' := by
    change IsEquivariantNX c c' a θN 1
    intro v
    change a (c.rhoNX 1 v) = c'.rhoNX (θN 1) (a v)
    rw [show θN (1 : ↥c.NX) = 1 from map_one θN, c.rhoNX_one, c'.rhoNX_one]
    rfl
  mul_mem' := by
    intro m n hm hn
    change IsEquivariantNX c c' a θN (m * n)
    intro v
    change a (c.rhoNX (m * n) v) = c'.rhoNX (θN (m * n)) (a v)
    have hm' : ∀ v, a (c.rhoNX m v) = c'.rhoNX (θN m) (a v) := by
      intro v; exact hm v
    have hn' : ∀ v, a (c.rhoNX n v) = c'.rhoNX (θN n) (a v) := by
      intro v; exact hn v
    rw [show θN (m * n) = θN m * θN n from map_mul θN m n,
      c.rhoNX_mul, c'.rhoNX_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hm' (c.rhoNX n v), hn' v]
  inv_mem' := by
    intro m hm
    change IsEquivariantNX c c' a θN m⁻¹
    intro v
    change a (c.rhoNX m⁻¹ v) = c'.rhoNX (θN m⁻¹) (a v)
    have hm' : ∀ v, a (c.rhoNX m v) = c'.rhoNX (θN m) (a v) := by
      intro v; exact hm v
    have harg : c.rhoNX m (c.rhoNX m⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← c.rhoNX_mul,
        show m * m⁻¹ = 1 from mul_inv_cancel m, c.rhoNX_one]
      rfl
    have h := hm' (c.rhoNX m⁻¹ v)
    rw [harg] at h
    have h2 : (c'.rhoNX (θN m))⁻¹ (a v) = a (c.rhoNX m⁻¹ v) := by
      rw [h, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    rw [show (c'.rhoNX (θN m))⁻¹ = c'.rhoNX (θN m⁻¹) from by
      rw [← c'.rhoNX_inv, show (θN m)⁻¹ = θN m⁻¹ from (map_inv θN m).symm]] at h2
    exact h2.symm

theorem Psub_eq_top {G : Type} [Group G] [Finite G] {z : G}
    {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z')
    (a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (θN : ↥c.NX ≃* ↥c'.NX)
    (t : G) (htN : t ∈ c.NX)
    (hCX : ∀ h : ↥c.CX, (⟨h, c.CX_le_NX h.2⟩ : ↥c.NX) ∈ Psub c c' a θN)
    (ht : (⟨t, htN⟩ : ↥c.NX) ∈ Psub c c' a θN)
    (hsup : c.NX = c.CX ⊔ Subgroup.zpowers t) :
    Psub c c' a θN = ⊤ := by
  rw [eq_top_iff]
  intro n _
  let S : Subgroup ↥c.NX := c.CX.subgroupOf c.NX
  let T : Subgroup ↥c.NX := (Subgroup.zpowers t).subgroupOf c.NX
  haveI hSnormal : S.Normal := c.CX_normal_NX
  have hST : S ⊔ T = ⊤ := by
    rw [show S ⊔ T = (c.CX ⊔ Subgroup.zpowers t).subgroupOf c.NX from by
      rw [Subgroup.subgroupOf_sup c.CX_le_NX (Subgroup.zpowers_le.mpr htN)]]
    rw [hsup, Subgroup.subgroupOf_self]
  have hnST : n ∈ S ⊔ T := by rw [hST]; exact Subgroup.mem_top n
  obtain ⟨x, hxS, y, hyT, hxy⟩ := Subgroup.mem_sup_of_normal_left.mp hnST
  have hxCX : (x : G) ∈ c.CX := hxS
  let xC : ↥c.CX := ⟨(x : G), hxCX⟩
  have hx_eq : x = (⟨xC, c.CX_le_NX xC.2⟩ : ↥c.NX) := Subtype.ext rfl
  have hxP : x ∈ Psub c c' a θN := by
    rw [hx_eq]
    exact hCX xC
  have hyz : (y : G) ∈ Subgroup.zpowers t := hyT
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
  have hy_eq : y = (⟨t, htN⟩ : ↥c.NX) ^ k := by
    apply Subtype.ext
    simpa using hk.symm
  have hyP : y ∈ Psub c c' a θN := by
    rw [hy_eq]
    exact Subgroup.zpowers_le.mpr ht (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  rw [← hxy]
  exact (Psub c c' a θN).mul_mem hxP hyP

theorem isometry_of_equivariant_CX
    (c : Loc49 G z) (c' : Loc49 G' z') (θ : ↥c.CX ≃* ↥c'.CX)
    (a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)
    (ha : ∀ (h : ↥c.CX) (v : c.S.Qt),
      a ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
        (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v)) (v : c.S.Qt) :
    c'.S.q (a v) = c.S.q v := by
  classical
  obtain ⟨x, -, hx⟩ := c.exists_x0_piC_hatM22Z
  let Γ : Set (c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) :=
    Set.range fun h : ↥c.CX => (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)
  let w : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt := c.wEquiv x
  have hw : w ∈ Γ := ⟨⟨x, c.X_le_CX x.2⟩, rfl⟩
  have hcomm : ∀ L : c.S.Qt →ₗ[ZMod 2] c.S.Qt, (∀ g ∈ Γ, ∀ v, L (g v) = g (L v)) →
      L = 0 ∨ L = LinearMap.id ∨ L = (w : c.S.Qt →ₗ[ZMod 2] c.S.Qt) ∨
        L = (w : c.S.Qt →ₗ[ZMod 2] c.S.Qt) ∘ₗ (w : c.S.Qt →ₗ[ZMod 2] c.S.Qt) := by
    intro L hL
    obtain ⟨e, rfl⟩ := c.exists_muLin_of_commute_CX L (fun h v => hL _ ⟨h, rfl⟩ v)
    rcases (by decide : ∀ e : FieldFour, e = 0 ∨ e = 1 ∨ e = ω ∨ e = ω₂) e with
      rfl | rfl | rfl | rfl
    · left
      ext v
      simp [Loc41.muLin_apply]
    · right; left
      ext v
      simp [Loc41.muLin_apply]
    · right; right; left
      ext v
      change c.muLin ω v = c.wEquiv x v
      rw [wEquiv_eq_mu c x hx, Loc41.muEquiv_apply, Loc41.muLin_apply]
    · right; right; right
      ext v
      change c.muLin ω₂ v = c.wEquiv x (c.wEquiv x v)
      rw [wEquiv_apply_wEquiv c x hx, Loc41.muEquiv_apply, Loc41.muLin_apply]
  have h₁ : ∀ g ∈ Γ, ∀ v, c.S.q (g v) = c.S.q v := by
    rintro _ ⟨h, rfl⟩ v
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (c.S.ρ (c.toSM h)).2 v
  let q₂ : QuadraticForm (ZMod 2) c.S.Qt := c'.S.q.comp a.toLinearMap
  have hq₂ : ∀ u, q₂ u = c'.S.q (a u) := fun u => rfl
  have h₂ : ∀ g ∈ Γ, ∀ v, q₂ (g v) = q₂ v := by
    rintro _ ⟨h, rfl⟩ v
    rw [hq₂, hq₂, ha h v]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (c'.S.ρ (c'.toSM (θ h))).2 (a v)
  have hne : q₂ ≠ 0 := by
    intro h0
    haveI : Nontrivial c'.S.Qt := by
      have hcard : Nat.card c'.S.Qt = 2 ^ 12 := by
        rw [Nat.card_congr c'.ψ.toEquiv, Nat.card_fun,
          CFSG.CharacterTheory.SteinbergBY.FieldFour.natCard_eq]
        norm_num
      exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    obtain ⟨u, hu⟩ := exists_ne (0 : c'.S.Qt)
    apply hu
    refine c'.S.q_nondegenerate.1 u fun u' => ?_
    have hq0 : ∀ t, c'.S.q t = 0 := fun t => by
      simpa [hq₂] using congrArg (fun q : QuadraticForm (ZMod 2) c.S.Qt => q (a.symm t)) h0
    rw [polarBilin_apply_apply, polar, hq0, hq0, hq0]
    simp
  have heq := CFSG.LinearAlgebra.eq_of_invariant_of_commutant hw (c.wEquiv_add x hx) hcomm h₁ h₂
    c.S.q_nondegenerate hne
  exact congrArg (fun q : QuadraticForm (ZMod 2) c.S.Qt => q v) heq

theorem exists_isometry_NX
    (c : Loc49 G z) (c' : Loc49 G' z')
    (θ : ↥c.CX ≃* ↥c'.CX) (hθ : ∀ h, c'.piC (θ h) = c.piC h)
    (θN : ↥c.NX ≃* ↥c'.NX)
    (hext : ∀ h : ↥c.CX, ((θN ⟨h, c.CX_le_NX h.2⟩ : ↥c'.NX) : G') = (θ h : G')) :
    ∃ a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt,
      (∀ v, c'.S.q (a v) = c.S.q v) ∧
      ∀ (n : ↥c.NX) (v : c.S.Qt),
        a ((c.S.ρ (c.toSMN n) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
          (c'.S.ρ (c'.toSMN (θN n)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v) := by
  classical
  obtain ⟨t, htN, htnotCX, ht2, htinv, hNXsup⟩ := c.exists_t
  let tNX : ↥c.NX := ⟨t, htN⟩
  let t' : ↥c'.NX := θN tNX
  obtain ⟨x0, hx0ne, hx0Z⟩ := c.exists_x0_piC_hatM22Z
  let x0CX : ↥c.CX := ⟨x0, c.X_le_CX x0.2⟩
  let x0NX : ↥c.NX := ⟨x0, c.X_le_NX x0.2⟩
  let x0' : ↥c'.CX := θ x0CX
  let x0NX' : ↥c'.NX := ⟨x0', c'.CX_le_NX x0'.2⟩
  let a0 : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt := Loc41.baseEquiv c.toLoc41 c'.toLoc41
  let A : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt :=
    (c'.S.ρ (c'.toSMN t') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)
  let B : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt :=
    (c'.S.ρ (c'.toSM x0') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)
  have hnotlin : ¬ ∃ γ ∈ hatM22Γ₀, ∀ v : c'.S.Qt,
      c'.ψ ((c'.S.ρ (c'.toSMN t') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v) =
        (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (c'.ψ v)) := by
    exact not_linear_toSMN c c' θ hθ θN hext tNX htinv x0 hx0Z
  rcases c'.linear_or_semilinear (c'.toSMN t') with hlin | hsemi
  · exact absurd hlin hnotlin
  · have hsem : ∀ (e : FieldFour) (he : e ≠ 0) (v : c'.S.Qt),
        A (c'.muEquiv e he v) =
          c'.muEquiv (e * e) (mul_ne_zero he he) (A v) := by
      intro e he v
      exact Loc41.semilinear_mu c'.toLoc41 A hsemi e he v
    let ρt : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt :=
      (c.S.ρ (c.toSMN tNX) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)
    let D : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt :=
      a0.symm.trans (ρt.trans (a0.trans A.symm))
    have hD_apply : ∀ v, D v = A.symm (a0 (ρt (a0.symm v))) := by
      intro v
      dsimp only [D]
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    have hD_comm : ∀ h' : ↥c'.CX, ∀ v : c'.S.Qt,
        D ((c'.S.ρ (c'.toSM h') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v) =
          (c'.S.ρ (c'.toSM h') : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (D v) := by
      intro h' v
      obtain ⟨h, rfl⟩ := θ.surjective h'
      have hconj_mem : (t : G) * (h : G) * (t : G)⁻¹ ∈ c.CX :=
        (Subgroup.normal_subgroupOf_iff c.CX_le_NX).mp c.CX_normal_NX
          (h : G) (t : G) h.2 htN
      let hconj : ↥c.CX := ⟨(t : G) * (h : G) * (t : G)⁻¹, hconj_mem⟩
      have htoSM_hconj : c.toSM hconj =
          c.toSMN tNX * c.toSM h * (c.toSMN tNX)⁻¹ := by
        apply Subtype.ext
        rfl
      have hρt_comm : (c.S.ρ (c.toSMN tNX) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) *
          (c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) =
          (c.S.ρ (c.toSM hconj) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) *
            (c.S.ρ (c.toSMN tNX) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) := by
        have h := congrArg (fun x : c.S.M => c.S.ρ x) htoSM_hconj
        rw [map_mul, map_mul, map_inv] at h
        have h' := congrArg (fun x : c.S.O =>
          (x : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)) h
        rw [h']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hρt_apply : ∀ w, (c.S.ρ (c.toSMN tNX) :
            c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)
          ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) w) =
          (c.S.ρ (c.toSM hconj) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt)
            ((c.S.ρ (c.toSMN tNX) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) w) := by
        intro w
        exact congrArg (fun e : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt => e w) hρt_comm
      have hθN_hconj : θN ⟨hconj, c.CX_le_NX hconj.2⟩ =
          t' * ⟨θ h, c'.CX_le_NX (θ h).2⟩ * t'⁻¹ := by
        have h1 : (⟨hconj, c.CX_le_NX hconj.2⟩ : ↥c.NX) =
            tNX * ⟨h, c.CX_le_NX h.2⟩ * tNX⁻¹ := by
          apply Subtype.ext
          rfl
        rw [h1]
        calc θN (tNX * ⟨h, c.CX_le_NX h.2⟩ * tNX⁻¹)
            = θN tNX * θN ⟨h, c.CX_le_NX h.2⟩ * θN tNX⁻¹ := by
                rw [map_mul, map_mul, map_inv]
          _ = t' * ⟨θ h, c'.CX_le_NX (θ h).2⟩ * t'⁻¹ := by
                rw [show θN ⟨h, c.CX_le_NX h.2⟩ =
                    ⟨θ h, c'.CX_le_NX (θ h).2⟩ from Subtype.ext (hext h)]
                dsimp only [t']
                rw [map_inv]
      have htoSM_hconj' : c'.toSM (θ hconj) =
          c'.toSMN t' * c'.toSM (θ h) * (c'.toSMN t')⁻¹ := by
        have h1 : c'.toSM (θ hconj) =
            c'.toSMN (θN ⟨hconj, c.CX_le_NX hconj.2⟩) := by
          apply Subtype.ext
          exact (hext hconj).symm
        rw [h1, hθN_hconj, c'.toSMN_mul, c'.toSMN_mul, c'.toSMN_inv,
          c'.toSMN_of_mem_CX]
      have hA_conj : (c'.S.ρ (c'.toSM (θ hconj)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) =
          A * (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) * A⁻¹ := by
        have h := congrArg (fun x : c'.S.M => c'.S.ρ x) htoSM_hconj'
        rw [map_mul, map_mul, map_inv] at h
        have h' := congrArg (fun x : c'.S.O =>
          (x : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)) h
        rw [h']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [show A = (c'.S.ρ (c'.toSMN t') :
          c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) from rfl]
      calc D ((c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v)
          = A.symm (a0 (ρt (a0.symm ((c'.S.ρ (c'.toSM (θ h)) :
              c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) v)))) := by rw [hD_apply]
        _ = A.symm (a0 (ρt ((c.S.ρ (c.toSM h) :
              c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (a0.symm v)))) := by
              rw [Loc41.baseEquiv_symm_equivariant c.toLoc41 c'.toLoc41 θ hθ h v]
        _ = A.symm (a0 ((c.S.ρ (c.toSM hconj) :
              c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) (ρt (a0.symm v)))) := by
              rw [hρt_apply]
        _ = A.symm ((c'.S.ρ (c'.toSM (θ hconj)) :
              c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a0 (ρt (a0.symm v)))) := by
              rw [Loc41.baseEquiv_equivariant c.toLoc41 c'.toLoc41 θ hθ hconj
                (ρt (a0.symm v))]
        _ = A.symm ((A * (c'.S.ρ (c'.toSM (θ h)) :
              c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) * A⁻¹) (a0 (ρt (a0.symm v)))) := by
              rw [hA_conj]
        _ = (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt)
              (A.symm (a0 (ρt (a0.symm v)))) := by
              rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
                LinearEquiv.symm_apply_apply, LinearEquiv.coe_inv]
        _ = (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (D v) := by
              rw [hD_apply]
    obtain ⟨e₀, he₀⟩ := c'.exists_muLin_of_commute_CX D.toLinearMap
      (fun h v => hD_comm h v)
    haveI hntQt : Nontrivial c'.S.Qt := by
      have hcard : Nat.card c'.S.Qt = 2 ^ 12 := by
        rw [Nat.card_congr c'.ψ.toEquiv, Nat.card_fun,
          CFSG.CharacterTheory.SteinbergBY.FieldFour.natCard_eq]
        norm_num
      exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    have he₀0 : e₀ ≠ 0 := by
      intro h0
      have hD0 : D.toLinearMap = 0 := by
        rw [he₀, h0]
        ext v
        simp [Loc41.muLin_apply]
      obtain ⟨w, hw⟩ := exists_ne (0 : c'.S.Qt)
      have hw0 : D (D.symm w) = 0 := by
        have := congrArg (fun L : c'.S.Qt →ₗ[ZMod 2] c'.S.Qt => L (D.symm w)) hD0
        simpa using this
      rw [LinearEquiv.apply_symm_apply] at hw0
      exact hw hw0
    have hD_eq : D = c'.muEquiv e₀ he₀0 := by
      apply LinearEquiv.ext
      intro v
      apply c'.ψLin.injective
      change c'.ψ (D v) = c'.ψ (c'.muEquiv e₀ he₀0 v)
      rw [show D v = c'.muLin e₀ v from
          congrArg (fun L : c'.S.Qt →ₗ[ZMod 2] c'.S.Qt => L v) he₀,
        c'.muLin_apply, c'.muEquiv_apply, AddEquiv.apply_symm_apply]
    have he₀3 : e₀ ^ 3 = 1 := by
      rcases (by decide : ∀ x : FieldFour, x ≠ 0 → x = 1 ∨ x = ω ∨ x = ω₂)
        e₀ he₀0 with h | h | h <;> rw [h] <;> decide
    let d : FieldFour := e₀⁻¹
    have hd : d ≠ 0 := inv_ne_zero he₀0
    have hd2 : d ^ 2 = e₀ := by
      dsimp only [d]
      field_simp
      exact he₀3.symm
    have hde : d * (e₀ * e₀) = e₀ := by
      dsimp only [d]
      field_simp
    let a : c.S.Qt ≃ₗ[ZMod 2] c'.S.Qt := a0.trans (c'.muEquiv d hd)
    have ha_apply : ∀ v, a v = c'.muEquiv d hd (a0 v) := by
      intro v
      rfl
    have ha_CX : ∀ h : ↥c.CX, ∀ v,
        a ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
          (c'.S.ρ (c'.toSM (θ h)) : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt) (a v) := by
      intro h v
      rw [ha_apply, ha_apply]
      rw [Loc41.baseEquiv_equivariant c.toLoc41 c'.toLoc41 θ hθ h v]
      exact congrArg (fun e : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt => e (a0 v))
        (c'.muEquiv_commute_rho_CX (θ h) d hd)
    have ha_t : ∀ v, a (ρt v) = A (a v) := by
      intro v
      have h1 : A.symm (a0 (ρt v)) = c'.muEquiv e₀ he₀0 (a0 v) := by
        have h := congrArg (fun e : c'.S.Qt ≃ₗ[ZMod 2] c'.S.Qt => e (a0 v)) hD_eq
        rw [show D (a0 v) = A.symm (a0 (ρt v)) from by
          rw [hD_apply, LinearEquiv.symm_apply_apply]] at h
        exact h
      have h2 : a0 (ρt v) =
          c'.muEquiv (e₀ * e₀) (mul_ne_zero he₀0 he₀0) (A (a0 v)) := by
        calc a0 (ρt v) = A (c'.muEquiv e₀ he₀0 (a0 v)) := by
              rw [← h1, LinearEquiv.apply_symm_apply]
          _ = c'.muEquiv (e₀ * e₀) (mul_ne_zero he₀0 he₀0) (A (a0 v)) :=
                hsem e₀ he₀0 (a0 v)
      calc a (ρt v) = c'.muEquiv d hd (a0 (ρt v)) := ha_apply (ρt v)
        _ = c'.muEquiv d hd (c'.muEquiv (e₀ * e₀) (mul_ne_zero he₀0 he₀0)
              (A (a0 v))) := by rw [h2]
        _ = c'.muEquiv (d * (e₀ * e₀))
              (mul_ne_zero hd (mul_ne_zero he₀0 he₀0)) (A (a0 v)) := by
              apply c'.ψLin.injective
              change c'.ψ (c'.muEquiv d hd (c'.muEquiv (e₀ * e₀) _ (A (a0 v)))) =
                c'.ψ (c'.muEquiv (d * (e₀ * e₀)) _ (A (a0 v)))
              rw [c'.muEquiv_apply_ψ, c'.muEquiv_apply_ψ, c'.muEquiv_apply_ψ, smul_smul]
        _ = c'.muEquiv e₀ he₀0 (A (a0 v)) := by
              rw [c'.muEquiv_apply, c'.muEquiv_apply, hde]
        _ = c'.muEquiv (d * d) (mul_ne_zero hd hd) (A (a0 v)) := by
              rw [c'.muEquiv_apply, c'.muEquiv_apply,
                show e₀ = d * d from by rw [← hd2, pow_two]]
        _ = A (c'.muEquiv d hd (a0 v)) := (hsem d hd (a0 v)).symm
        _ = A (a v) := by rw [ha_apply]
    have hCXgen : ∀ h : ↥c.CX,
        (⟨h, c.CX_le_NX h.2⟩ : ↥c.NX) ∈ Psub c c' a θN := by
      intro h
      change IsEquivariantNX c c' a θN ⟨h, c.CX_le_NX h.2⟩
      intro v
      change a (c.rhoNX ⟨h, c.CX_le_NX h.2⟩ v) =
        c'.rhoNX (θN ⟨h, c.CX_le_NX h.2⟩) (a v)
      rw [c.rhoNX_of_mem_CX,
        show θN ⟨h, c.CX_le_NX h.2⟩ = ⟨θ h, c'.CX_le_NX (θ h).2⟩ from
          Subtype.ext (hext h),
        c'.rhoNX_of_mem_CX]
      exact ha_CX h v
    have htP : tNX ∈ Psub c c' a θN := by
      change IsEquivariantNX c c' a θN tNX
      intro v
      change a (c.rhoNX tNX v) = c'.rhoNX (θN tNX) (a v)
      exact ha_t v
    have hPtop : Psub c c' a θN = ⊤ :=
      Psub_eq_top c c' a θN t htN hCXgen htP hNXsup
    have hP_all : ∀ n : ↥c.NX, IsEquivariantNX c c' a θN n := by
      intro n
      have hnP : n ∈ Psub c c' a θN := hPtop.symm ▸ Subgroup.mem_top n
      exact hnP
    exact ⟨a, isometry_of_equivariant_CX c c' θ a ha_CX, fun n v => hP_all n v⟩
end Loc49

end CFSG.Quasithin.H13.AS91
