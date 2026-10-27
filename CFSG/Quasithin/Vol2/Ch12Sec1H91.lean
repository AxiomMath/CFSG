module

public import CFSG.Quasithin.Vol2.Ch12Sec1Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def LemH91 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) →
      (∃ v₁ : G, V₁ ⊓ Subgroup.centralizer
          ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) =
        Subgroup.zpowers v₁) ∧
      ∃ β : G → G → ZMod 2, IsDualPairing121 L V₁ V₂ β ∧
        ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 →
          ((∃ m ∈ Subgroup.normalizer (L : Set G), m * v * m⁻¹ = w) ↔
            (((v ∈ V₁ ∨ v ∈ V₂) ↔ (w ∈ V₁ ∨ w ∈ V₂)) ∧
              (IsNonsingular121 V₁ V₂ β v ↔ IsNonsingular121 V₁ V₂ β w)))

end CFSG.Quasithin.H13
