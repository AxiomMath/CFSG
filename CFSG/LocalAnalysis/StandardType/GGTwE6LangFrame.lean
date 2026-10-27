module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRankOne

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6

namespace TwE6Lang

theorem mul_rearrange_four {X : Type*} [Group X] {g₀ g₁ g₂ g₃ m₀ m₁ m₂ m₃ : X}
    (h01 : Commute m₀ g₁) (h02 : Commute m₀ g₂) (h03 : Commute m₀ g₃) (h12 : Commute m₁ g₂)
    (h13 : Commute m₁ g₃) (h23 : Commute m₂ g₃) :
    g₀ * m₀ * (g₁ * m₁) * (g₂ * m₂) * (g₃ * m₃) = g₀ * g₁ * g₂ * g₃ * (m₀ * m₁ * m₂ * m₃) := by
  simp only [mul_assoc]
  rw [h01.left_comm, h12.left_comm, h02.left_comm, h23.left_comm, h13.left_comm,
    h03.left_comm]


@[expose] def frameWord : Fin 4 → List (Fin (Tag.rank .F4)) :=
  ![[], [nf 1, nf 2, nf 1], [nf 3, nf 1, nf 2, nf 1], [nf 2, nf 3, nf 1, nf 2, nf 1]]

@[expose] def frameRoot : Fin 4 → Fin (Tag.rank .E6) → ℤ :=
  ![![0, 1, 0, 0, 0, 0], ![0, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 2, 1]]

theorem wAct_frameWord (j : Fin 4) : wAct (frameWord j) eOne = frameRoot j := by
  fin_cases j <;> decide

theorem isRoot_frameRoot (j : Fin 4) : IsRoot .E6 (frameRoot j) := by
  rw [← wAct_frameWord]
  exact isRoot_wAct _ (IsRoot.basis _)

theorem frame_cond (i j : Fin 4) (hij : i ≠ j) :
    (frameRoot i + frameRoot j ≠ 0 ∧
      MinData.toWeight (frameRoot i + frameRoot j) ⬝ᵥ (frameRoot i + frameRoot j) ≠ 2) ∧
    (frameRoot i + -frameRoot j ≠ 0 ∧
      MinData.toWeight (frameRoot i + -frameRoot j) ⬝ᵥ (frameRoot i + -frameRoot j) ≠ 2) ∧
    (-frameRoot i + frameRoot j ≠ 0 ∧
      MinData.toWeight (-frameRoot i + frameRoot j) ⬝ᵥ (-frameRoot i + frameRoot j) ≠ 2) ∧
    (-frameRoot i + -frameRoot j ≠ 0 ∧
      MinData.toWeight (-frameRoot i + -frameRoot j) ⬝ᵥ (-frameRoot i + -frameRoot j) ≠ 2) := by
  revert i j
  decide

variable {k : Type*} [Field k]

theorem commute_frame {i j : Fin 4} (hij : i ≠ j) {x y : e6Data_valid.minGroup k}
    (hx : x ∈ rankOne k (frameRoot i)) (hy : y ∈ rankOne k (frameRoot j)) : Commute x y := by
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, ⟨a₃, b₃⟩, ⟨a₄, b₄⟩⟩ := frame_cond i j hij
  exact commute_of_mem_rankOne (isRoot_frameRoot i) (isRoot_frameRoot j)
    ⟨a₁, not_isRoot_of_form b₁⟩ ⟨a₂, not_isRoot_of_form b₂⟩ ⟨a₃, not_isRoot_of_form b₃⟩
    ⟨a₄, not_isRoot_of_form b₄⟩ hx hy

variable (k) in
@[expose] noncomputable def frameG (θ : k →+* k) (l : k) (j : Fin 4) : e6Data_valid.minGroup k :=
  nWord k (frameWord j) * langOne k θ l * (nWord k (frameWord j))⁻¹

variable (k) in
@[expose] noncomputable def frameM (t : kˣ) (j : Fin 4) : e6Data_valid.minGroup k :=
  nWord k (frameWord j) * langM k t * (nWord k (frameWord j))⁻¹

variable (k) in
@[expose] noncomputable def langG (θ : k →+* k) (l : k) : e6Data_valid.minGroup k :=
  frameG k θ l 0 * frameG k θ l 1 * frameG k θ l 2 * frameG k θ l 3

variable (k) in
@[expose] noncomputable def langMM (t : kˣ) : e6Data_valid.minGroup k :=
  frameM k t 0 * frameM k t 1 * frameM k t 2 * frameM k t 3

theorem frameG_mem (θ : k →+* k) (l : k) (j : Fin 4) :
    frameG k θ l j ∈ rankOne k (frameRoot j) := by
  rw [frameG, ← wAct_frameWord]
  exact nWord_conj_mem_rankOne _ (IsRoot.basis _) (langOne_mem_rankOne θ l)

theorem frameM_mem (t : kˣ) (j : Fin 4) : frameM k t j ∈ rankOne k (frameRoot j) := by
  rw [frameM, ← wAct_frameWord]
  exact nWord_conj_mem_rankOne _ (IsRoot.basis _) (langM_mem_rankOne t)

theorem langG_mem_normalizer_rankOne (θ : k →+* k) (l : k) :
    langG k θ l ∈ Subgroup.normalizer
      (rankOne k (frameRoot 0) : Set (e6Data_valid.minGroup k)) := by
  let N := Subgroup.normalizer (rankOne k (frameRoot 0) : Set (e6Data_valid.minGroup k))
  have hN (j : Fin 4) : frameG k θ l j ∈ N := by
    by_cases hj : j = 0
    · subst j
      exact (rankOne k (frameRoot 0)).le_normalizer (frameG_mem θ l 0)
    · apply Subgroup.centralizer_le_normalizer _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (commute_frame hj (frameG_mem θ l j) hz).symm.eq
  exact N.mul_mem (N.mul_mem (N.mul_mem (hN 0) (hN 1)) (hN 2)) (hN 3)

theorem sigma_frameG (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l) (j : Fin 4) :
    sigma k θ (frameG k θ l j) = frameG k θ l j * frameM k (negDelta θ hl) j := by
  rw [frameG, frameM, map_mul, map_mul, map_inv, sigma_nWord, sigma_langOne θ hθ hl]
  group

theorem sigma_langG (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l) :
    sigma k θ (langG k θ l) = langG k θ l * langMM k (negDelta θ hl) := by
  rw [langG, map_mul, map_mul, map_mul, sigma_frameG θ hθ hl, sigma_frameG θ hθ hl,
    sigma_frameG θ hθ hl, sigma_frameG θ hθ hl, langMM]
  exact mul_rearrange_four
    (commute_frame (by decide) (frameM_mem _ 0) (frameG_mem θ l 1))
    (commute_frame (by decide) (frameM_mem _ 0) (frameG_mem θ l 2))
    (commute_frame (by decide) (frameM_mem _ 0) (frameG_mem θ l 3))
    (commute_frame (by decide) (frameM_mem _ 1) (frameG_mem θ l 2))
    (commute_frame (by decide) (frameM_mem _ 1) (frameG_mem θ l 3))
    (commute_frame (by decide) (frameM_mem _ 2) (frameG_mem θ l 3))

@[expose] def frameAct (j : Fin 4) : (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ) :=
  (wAct (frameWord j)).comp ((reflectHom .E6 (nd 1)).comp (wActInv (frameWord j)))

@[expose] def frameW : (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ) :=
  (frameAct 0).comp ((frameAct 1).comp ((frameAct 2).comp (frameAct 3)))

theorem frameW_comp_rho : frameW.comp rhoHom = -AddMonoidHom.id _ :=
  addMonoidHom_ext_single fun l => by
    revert l
    decide +kernel

theorem frameW_rho (v : Fin (Tag.rank .E6) → ℤ) : frameW (rho v) = -v :=
  DFunLike.congr_fun frameW_comp_rho v

theorem hm_commute_torusPow (a : Fin (Tag.rank .E6)) (t ζ : kˣ) (w : Fin (Tag.rank .E6) → ℤ) :
    Commute (e6Data_valid.hm k a t) (torusPow ζ w) :=
  hm_commute_torusHom a t _

theorem langM_conj_torusPow (t ζ : kˣ) (w : Fin (Tag.rank .E6) → ℤ) :
    langM k t * torusPow ζ w * (langM k t)⁻¹ = torusPow ζ (reflect .E6 (nd 1) w) := by
  have hc : e6Data_valid.hm k (nd 1) t * torusPow ζ w * (e6Data_valid.hm k (nd 1) t)⁻¹ =
      torusPow ζ w := by
    rw [(hm_commute_torusPow (nd 1) t ζ w).eq, mul_inv_cancel_right]
  rw [langM, show e6Data_valid.nm k (nd 1) * e6Data_valid.hm k (nd 1) t * torusPow ζ w *
      (e6Data_valid.nm k (nd 1) * e6Data_valid.hm k (nd 1) t)⁻¹ =
      e6Data_valid.nm k (nd 1) * (e6Data_valid.hm k (nd 1) t * torusPow ζ w *
        (e6Data_valid.hm k (nd 1) t)⁻¹) * (e6Data_valid.nm k (nd 1))⁻¹ by group, hc,
    nm_conj_torusPow]

theorem frameM_conj_torusPow (t ζ : kˣ) (j : Fin 4) (w : Fin (Tag.rank .E6) → ℤ) :
    frameM k t j * torusPow ζ w * (frameM k t j)⁻¹ = torusPow ζ (frameAct j w) := by
  rw [frameM, show nWord k (frameWord j) * langM k t * (nWord k (frameWord j))⁻¹ * torusPow ζ w *
      (nWord k (frameWord j) * langM k t * (nWord k (frameWord j))⁻¹)⁻¹ =
      nWord k (frameWord j) * (langM k t * ((nWord k (frameWord j))⁻¹ * torusPow ζ w *
        nWord k (frameWord j)) * (langM k t)⁻¹) * (nWord k (frameWord j))⁻¹ by group,
    nWord_inv_conj_torusPow, langM_conj_torusPow, nWord_conj_torusPow]
  rfl

theorem langMM_conj_torusPow (t ζ : kˣ) (w : Fin (Tag.rank .E6) → ℤ) :
    langMM k t * torusPow ζ w * (langMM k t)⁻¹ = torusPow ζ (frameW w) := by
  rw [langMM, show frameM k t 0 * frameM k t 1 * frameM k t 2 * frameM k t 3 * torusPow ζ w *
      (frameM k t 0 * frameM k t 1 * frameM k t 2 * frameM k t 3)⁻¹ =
      frameM k t 0 * (frameM k t 1 * (frameM k t 2 * (frameM k t 3 * torusPow ζ w *
        (frameM k t 3)⁻¹) * (frameM k t 2)⁻¹) * (frameM k t 1)⁻¹) * (frameM k t 0)⁻¹ by group,
    frameM_conj_torusPow, frameM_conj_torusPow, frameM_conj_torusPow, frameM_conj_torusPow]
  rfl

theorem sigma_langG_conj_torusPow (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l)
    {ζ : kˣ} {m : ℤ} (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (v : Fin (Tag.rank .E6) → ℤ) :
    sigma k θ (langG k θ l * torusPow ζ v * (langG k θ l)⁻¹) =
      langG k θ l * torusPow ζ (-(m • v)) * (langG k θ l)⁻¹ := by
  rw [map_mul, map_mul, map_inv, sigma_langG θ hθ hl, sigma_torusPow θ hζ,
    show langG k θ l * langMM k (negDelta θ hl) * torusPow ζ (m • rho v) *
      (langG k θ l * langMM k (negDelta θ hl))⁻¹ = langG k θ l * (langMM k (negDelta θ hl) *
        torusPow ζ (m • rho v) * (langMM k (negDelta θ hl))⁻¹) * (langG k θ l)⁻¹ by group,
    langMM_conj_torusPow, map_zsmul, frameW_rho, smul_neg]

end TwE6Lang

end CFSG.StandardType
