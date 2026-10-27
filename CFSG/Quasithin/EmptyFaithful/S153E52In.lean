module

public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input15352 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (a : MulAut V), G64.Hyp61 G a →
      Nat.card ↥(commV (Subgroup.zpowers a)) = 2 →
      (∃ T' : Subgroup (MulAut V), IsSylowTwoOf T' G ∧ a ∈ T' ∧ ∀ x ∈ T', x * a = a * x) →
      (∀ g ∈ G, orderOf g = 3 → ∃ w ∈ commV (Subgroup.zpowers a), g w ≠ w) →
      Nat.card V = 4

end CFSG.Quasithin
