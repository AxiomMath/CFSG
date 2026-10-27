module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRank

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6

namespace TwE6Lang

theorem mul_rearrange_three {X : Type*} [Group X] {g₁ g₂ g₃ m₁ m₂ m₃ : X}
    (h12 : Commute m₁ g₂) (h13 : Commute m₁ g₃) (h23 : Commute m₂ g₃) :
    g₁ * m₁ * (g₂ * m₂) * (g₃ * m₃) = g₁ * g₂ * g₃ * (m₁ * m₂ * m₃) := by
  simp only [mul_assoc]
  rw [h12.left_comm, h23.left_comm, h13.left_comm]


variable {k : Type*} [Field k]

variable (k) in
@[expose] noncomputable def langG3 (θ : k →+* k) (l : k) : e6Data_valid.minGroup k :=
  frameG k θ l 1 * frameG k θ l 2 * frameG k θ l 3

variable (k) in
@[expose] noncomputable def langMM3 (t : kˣ) : e6Data_valid.minGroup k :=
  frameM k t 1 * frameM k t 2 * frameM k t 3

theorem sigma_langG3 (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l) :
    sigma k θ (langG3 k θ l) = langG3 k θ l * langMM3 k (negDelta θ hl) := by
  rw [langG3, map_mul, map_mul, sigma_frameG θ hθ hl, sigma_frameG θ hθ hl,
    sigma_frameG θ hθ hl, langMM3]
  exact mul_rearrange_three
    (commute_frame (by decide) (frameM_mem _ 1) (frameG_mem θ l 2))
    (commute_frame (by decide) (frameM_mem _ 1) (frameG_mem θ l 3))
    (commute_frame (by decide) (frameM_mem _ 2) (frameG_mem θ l 3))

@[expose] def frameW3 : (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ) :=
  (frameAct 1).comp ((frameAct 2).comp (frameAct 3))

theorem frameAct_zero (v : Fin (Tag.rank .E6) → ℤ) : frameAct 0 v = reflect .E6 (nd 1) v := by
  rfl

theorem frameW3_comp_rho : frameW3.comp rhoHom = -(frameAct 0) :=
  addMonoidHom_ext_single fun l => by
    revert l
    decide +kernel

theorem frameW3_rho (v : Fin (Tag.rank .E6) → ℤ) : frameW3 (rho v) = -(frameAct 0 v) :=
  DFunLike.congr_fun frameW3_comp_rho v

theorem langMM3_conj_torusPow (t ζ : kˣ) (w : Fin (Tag.rank .E6) → ℤ) :
    langMM3 k t * torusPow ζ w * (langMM3 k t)⁻¹ = torusPow ζ (frameW3 w) := by
  rw [langMM3, show frameM k t 1 * frameM k t 2 * frameM k t 3 * torusPow ζ w *
      (frameM k t 1 * frameM k t 2 * frameM k t 3)⁻¹ =
      frameM k t 1 * (frameM k t 2 * (frameM k t 3 * torusPow ζ w *
        (frameM k t 3)⁻¹) * (frameM k t 2)⁻¹) * (frameM k t 1)⁻¹ by group,
    frameM_conj_torusPow, frameM_conj_torusPow, frameM_conj_torusPow]
  rfl

theorem sigma_langG3_conj_torusPow (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l)
    {ζ : kˣ} {m : ℤ} (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (v : Fin (Tag.rank .E6) → ℤ) :
    sigma k θ (langG3 k θ l * torusPow ζ v * (langG3 k θ l)⁻¹) =
      langG3 k θ l * torusPow ζ (-(m • frameAct 0 v)) * (langG3 k θ l)⁻¹ := by
  rw [map_mul, map_mul, map_inv, sigma_langG3 θ hθ hl, sigma_torusPow θ hζ,
    show langG3 k θ l * langMM3 k (negDelta θ hl) * torusPow ζ (m • rho v) *
      (langG3 k θ l * langMM3 k (negDelta θ hl))⁻¹ =
      langG3 k θ l * (langMM3 k (negDelta θ hl) * torusPow ζ (m • rho v) *
        (langMM3 k (negDelta θ hl))⁻¹) * (langG3 k θ l)⁻¹ by group,
    langMM3_conj_torusPow, map_zsmul, frameW3_rho, smul_neg]

theorem frameRoot_zero : frameRoot 0 = eOne := by
  funext a
  fin_cases a <;> decide

theorem commute_langG3 (θ : k →+* k) (l : k) {x : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne k eOne) : Commute x (langG3 k θ l) := by
  have hx' : x ∈ rankOne k (frameRoot 0) := by
    rw [frameRoot_zero]
    exact hx
  rw [langG3]
  exact Commute.mul_right
    (Commute.mul_right
      (commute_frame (by decide) hx' (frameG_mem θ l 1))
      (commute_frame (by decide) hx' (frameG_mem θ l 2)))
    (commute_frame (by decide) hx' (frameG_mem θ l 3))

end TwE6Lang

end CFSG.StandardType
