module

public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def DerivedG2WeakClosureRad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    KindG2 L (fsuV T I) n → fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
    ∀ g : G, conjSubgroup (fsuV T I) g ≤ T →
      conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (fsuV T I : Set G)

end CFSG.Quasithin.Vol2.Ch11.SecB
