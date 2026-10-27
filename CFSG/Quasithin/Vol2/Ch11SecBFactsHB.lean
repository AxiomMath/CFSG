module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

@[expose] def FactBorelComm : Prop :=
  ∀ (Y Y' : Type) [Group Y] [Finite Y] [Group Y'] [Finite Y'] (n : ℕ) (φ : Y →* Y'),
    2 ≤ n → Function.Surjective φ → commutator Y = ⊤ → φ.ker ≤ Subgroup.center Y →
    Odd (Nat.card φ.ker) → (E2.IsBenderOf n Y' ∨ IsPSL 3 2 n Y' ∨ IsPSp4 2 n Y') →
    ∀ S' : Subgroup Y', IsSylowTwoOf S' ⊤ →
      IsPGroup 2 ↥⁅(Subgroup.normalizer (S' : Set Y')).comap φ,
        (Subgroup.normalizer (S' : Set Y')).comap φ⁆

end CFSG.Quasithin.Vol2.Ch11.SecB
