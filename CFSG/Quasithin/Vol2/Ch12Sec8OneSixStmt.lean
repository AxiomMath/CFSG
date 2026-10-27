module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def A7NatFact12813 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ S : Subgroup (V ≃ₗ[ZMod 2] V)) (v : V),
    G112Concl4 Γ → (∀ x, B x x = 0) → (∀ x, (∀ y, B x y = 0) → x = 0) →
    (∀ γ ∈ Γ, ∀ x y, B (γ x) (γ y) = B x y) → QuasithinUnique.IsSylowTwoOf S Γ → v ≠ 0 →
    (∀ s ∈ S, s v = v) →
    ∃ Up : Submodule (ZMod 2) V, (∀ s ∈ S, ∀ u ∈ Up, s u ∈ Up) ∧ (∀ u ∈ Up, B v u = 0) ∧
      v ∉ Up ∧
      ((∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ S → IsElemAbelian 2 A →
          (∀ a ∈ A, ∀ u ∈ Up, a u = u) → Nat.card A ≤ 2) ∨
        ((∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ S → IsElemAbelian 2 A →
            (∀ a ∈ A, ∀ u ∈ Up, a u = u) → Nat.card A ≤ 4) ∧
          ∃ Y : Subgroup (V ≃ₗ[ZMod 2] V), Y ≤ Γ ∧ (∀ y ∈ Y, y v = v) ∧ IsElemAbelian 3 Y ∧
            Nat.card Y = 9))

@[expose] def Lemma12_8_13_six_hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → 4 ≤ n → ∀ D : HatModelU (u128 V V₁),
      ¬ G112Concl4 (D.img (Subgroup.normalizer (V₁ : Set G)))

end CFSG.Quasithin.H13
