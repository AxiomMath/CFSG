module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint

@[expose] def FactType513ThreeJ4 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Q R S B D : Subgroup A), Star513 Q R S B D →
    IsSporadic .J4 ↥Q →
    (∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) →
    D ≤ Subgroup.normalizer (R : Set A)

end CFSG.Quasithin.H13
