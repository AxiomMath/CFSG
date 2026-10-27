module

public import CFSG.Assembly.InCatalog

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG
open CFSG.Assembly (InCatalog)

structure NHyp {G : Type} [Group G] (Q L : Subgroup G) (b : G) : Prop where
  kgroup : KCore.KGroupNonab InCatalog ↥Q
  iso : Nonempty (L ≃* GL (Fin 3) (ZMod 2))
  normalizes : L ≤ Subgroup.normalizer (Q : Set G)
  coprime : Nat.Coprime 3 (Nat.card Q)
  mem : b ∈ L
  order : orderOf b = 3
  cent : Q ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (L : Set G)

@[expose] def NLeast {G : Type} [Group G] (Q L : Subgroup G) : Prop :=
  ∀ R : Subgroup G, R ≤ Q → (∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R) →
    (∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) → R = ⊥ ∨ R = Q

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
