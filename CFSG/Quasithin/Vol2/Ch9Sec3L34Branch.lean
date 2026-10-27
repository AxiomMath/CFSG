module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch9Sec2Z

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

@[expose] def Ch9L34Branch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Setup T L I 2 →
    zQ T I = fsuV T I → ∀ H K B D : Subgroup G, IsHStar T (fsuM T L) H → E1.nParam H = 2 →
    H = K ⊔ T → K ∈ cComp H → T ≤ Subgroup.normalizer (K : Set G) →
    IsPGroup 2 (kerIn (H ⊓ fsuM T L) H) → IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K) →
    Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) → B ≤ K → Nat.card B = 3 →
    B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) →
    B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) → False

end CFSG.Quasithin.H13.Ch9
