module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open CFSG.Open

@[expose] def StatedConjActionPCore (p : ℕ) {G : Type*} [Group G] (P : Subgroup G) [P.Normal] :
    Subgroup G :=
  (pCore p (G ⧸ Subgroup.centralizer (P : Set G))).comap (QuotientGroup.mk' _)

@[expose] def StatedConjPStable (p : ℕ) {G : Type*} [Group G] (P : Subgroup G) [P.Normal] : Prop :=
  ∀ x : G,
    (∀ u ∈ P, (u⁻¹ * x⁻¹ * u * x)⁻¹ * x⁻¹ * (u⁻¹ * x⁻¹ * u * x) * x = 1) →
      x ∈ StatedConjActionPCore p P

end CFSG.Open
