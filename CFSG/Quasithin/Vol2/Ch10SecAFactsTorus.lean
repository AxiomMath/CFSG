module

public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def FactSzTorus : Prop :=
  ∀ (V : Type) [CommGroup V] (H : Subgroup (MulAut V)) (f : ℕ), BinaryNaturalSz H ⊤ ⊥ f →
    ∀ P : Subgroup (MulAut V), IsSylowTwoOf P H →
      ∀ φ ∈ H, φ ∈ Subgroup.normalizer (P : Set (MulAut V)) → Odd (orderOf φ) →
        ∀ v : V, v ≠ 1 → (∀ p ∈ P, p v = v) → φ v = v → φ = 1

@[expose] def FactOrthTorus : Prop :=
  ∀ (V : Type) [CommGroup V] (H : Subgroup (MulAut V)) (n : ℕ), BinaryOrthogonalFour H ⊤ ⊥ n →
    ∀ P : Subgroup (MulAut V), IsSylowTwoOf P H →
      ∀ A : Subgroup (MulAut V), A ≤ H → A ≤ Subgroup.normalizer (P : Set (MulAut V)) →
        Odd (Nat.card A) → ∀ v : V, v ≠ 1 → (∀ p ∈ P, p v = v) → (∀ a ∈ A, a v = v) →
          ∃ f : ↥A →* Multiplicative (ZMod (2 ^ n + 1)), Function.Injective f

structure FactsTorus : Prop where
  sz : FactSzTorus
  orth : FactOrthTorus

end CFSG.Quasithin.Vol2.Ch10.SecA
