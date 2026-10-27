module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin

@[expose] def FactBorelOddLarge : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (m : ℕ),
    ((2 ≤ m ∧ IsPSU 3 2 m Y) ∨ (3 ≤ m ∧ IsPSL 3 2 m Y) ∨ (2 ≤ m ∧ IsPSp4 2 m Y)) →
    ∀ S : Subgroup Y, QuasithinUnique.IsSylowTwoOf S ⊤ →
      2 ^ m - 1 < S.relIndex (Subgroup.normalizer (S : Set Y))

@[expose] def FactBenderCartanFrob : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (m : ℕ), 2 ≤ m → (IsPSL 2 2 m Y ∨ IsSz m Y) →
    ∀ S : Subgroup Y, QuasithinUnique.IsSylowTwoOf S ⊤ →
    ∀ d ∈ Subgroup.normalizer (S : Set Y), orderOf d = 2 ^ m - 1 →
    ∀ α : MulAut Y, (∃ k : ℕ, α ^ 2 ^ k = 1) → S.map α.toMonoidHom = S →
      α d ∈ Subgroup.zpowers d → ∃ j : ℕ, α d = d ^ 2 ^ j

end CFSG.Quasithin.H13.Ch9
