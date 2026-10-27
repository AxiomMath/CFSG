module

public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Open CFSG.QuasithinUnique

@[expose] def StmtH12_1HatM22 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X L S : Subgroup (MulAut W), L ≤ X → X ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      Subgroup.centralizer (L : Set (MulAut W)) ⊓ X ≤ L → Mhat22Twelve L ⊤ ⊥ →
      IsSylowTwoOf S X → X = L ⊔ S →
      (∃ s ∈ S, ∃ z ∈ Subgroup.center ↥L, s * (z : MulAut W) * s⁻¹ ≠ (z : MulAut W)) →
        Nat.card ↥(fixV S) = 2 ∧
          ∃ P : Subgroup (MulAut W), S ≤ P ∧ P ≤ X ∧ (Subgroup.center ↥L).map L.subtype ≤ P ∧
            Group.IsSolvable ↥P ∧
            ∀ Y : Subgroup W, Nat.card ↥Y = 4 → fixV S ≤ Y →
              (∀ z ∈ Subgroup.center ↥L, ∀ y ∈ Y, (z : MulAut W) y ∈ Y) →
                ¬ ∀ p ∈ P, ∀ y ∈ Y, p y ∈ Y

end CFSG.Quasithin.H.Mathieu
