module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightImg

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ModData

variable {H E F : Subgroup G} (M : ModData H E F)

theorem img_mono {S S' : Subgroup G} (h : S ≤ S') : M.img S ≤ M.img S' := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := M.mem_img.1 hr
  exact M.mem_img.2 ⟨x, h hx, rfl⟩

theorem img_le_range (S : Subgroup G) : M.img S ≤ M.ρ.range :=
  Subgroup.map_le_range _ _

theorem isElemAbelian_img {S : Subgroup G} (hS : IsElemAbelian 2 S) :
    IsElemAbelian 2 (M.img S) :=
  (hS.subgroupOf H).map M.ρ

theorem exists_two_orbit_of_comm_ne {A X : Subgroup G} (hAH : A ≤ H) (hXH : X ≤ H)
    (hA : IsElemAbelian 2 A) (hX : Odd (Nat.card X))
    (hXn : H ≤ normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G))
    (hidx : 4 ≤ ((A ⊓ centralizerQuot H E F).subgroupOf A).index)
    (hcomm : ¬ ⁅X, A⁆ ≤ centralizerQuot H E F) :
    ∃ (a₁ : ↥H) (w : M.W), (a₁ : G) ∈ A ∧ M.ρ a₁ w ≠ w ∧
      ∀ b : ↥H, (b : G) ∈ A → M.ρ b w = w ∨ M.ρ b w = M.ρ a₁ w := by
  have hn := M.range_le_normalizer_img hXH hXn
  have hAn : M.img A ≤ normalizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) :=
    (M.img_le_range A).trans hn
  obtain ⟨r₁, w, hr₁, hmv, horb⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_two_orbit_of_comm_ne
    (M.isElemAbelian_img hA)
    (by rw [M.card_img hAH]; exact hidx) hAn (M.odd_card_img hX)
    (M.img_commutator_ne_bot hXH hAH hcomm)
  obtain ⟨a₁, ha₁A, rfl⟩ := M.mem_img.1 hr₁
  exact ⟨a₁, w, ha₁A, hmv, fun b hb => horb _ (M.mem_img.2 ⟨b, hb, rfl⟩)⟩

theorem exists_two_orbit_conf {A X T : Subgroup G} (hFE : F < E) (hAT : A ≤ T) (hTH : T ≤ H)
    (hXH : X ≤ H) (hXT : X ⊔ T = H) (hT : IsPGroup 2 T) (hA : IsElemAbelian 2 A)
    (hX : Odd (Nat.card X)) (hXn : H ≤ normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G))
    (hidx : 4 ≤ ((A ⊓ centralizerQuot H E F).subgroupOf A).index)
    (hquad : ∀ a b : ↥H, (a : G) ∈ A → (b : G) ∈ A → ∀ w : M.W,
      M.ρ a (M.ρ b w - w) = M.ρ b w - w) :
    ∃ (a₁ y : ↥H) (w : M.W), (a₁ : G) ∈ A ∧ (y : G) ∈ X ∧ M.ρ y ≠ 1 ∧ M.ρ a₁ w ≠ w ∧
      (∀ b : ↥H, (b : G) ∈ A → M.ρ b w = w ∨ M.ρ b w = M.ρ a₁ w) ∧
      M.ρ y (M.ρ a₁ w - w) = M.ρ a₁ w - w := by
  have hAH : A ≤ H := hAT.trans hTH
  have hn := M.range_le_normalizer_img hXH hXn
  have hAn : M.img A ≤ normalizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) :=
    (M.img_le_range A).trans hn
  have hC : M.img A ⊓ centralizer ((M.img X : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ (M.img_mono hAT)).trans
      (M.img_inf_centralizer_eq_bot hFE hTH hXH hXT hT hn).le)
  have hquad' : ∀ a ∈ M.img A, ∀ b ∈ M.img A, ∀ w : M.W, a (b w - w) = b w - w := by
    rintro _ ha _ hb w
    obtain ⟨a, haA, rfl⟩ := M.mem_img.1 ha
    obtain ⟨b, hbA, rfl⟩ := M.mem_img.1 hb
    exact hquad a b haA hbA w
  obtain ⟨r₁, r₂, w, hr₁, hr₂, hr₂1, hmv, horb, hfix⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_two_orbit_conf (M.isElemAbelian_img hA)
    (M.odd_card_img hX) hAn hC (by rw [M.card_img hAH]; exact hidx) hquad'
  obtain ⟨a₁, ha₁A, rfl⟩ := M.mem_img.1 hr₁
  obtain ⟨y, hyX, rfl⟩ := M.mem_img.1 hr₂
  exact ⟨a₁, y, w, ha₁A, hyX, hr₂1, hmv, fun b hb => horb _ (M.mem_img.2 ⟨b, hb, rfl⟩), hfix⟩

end ModData

end CFSG.LocalAnalysis.WeakClosure81

end
