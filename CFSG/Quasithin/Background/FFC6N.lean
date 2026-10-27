module

public import CFSG.Quasithin.Background.B56Inputs
public import CFSG.Quasithin.Background.FFC4Three

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def B57Input : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G → ¬ ThreeRank2 ↥L

@[expose] def B59Last : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L : Subgroup (MulAut V), IsFFStarMin G A → CFSG.Open.IsComponentOf L G → ⁅L, A⁆ = L →
      (∃ m, Odd m ∧ BinaryNaturalSL L (commSub (fixV (pCoreOf 2 (L ⊔ A))) L) ⊥ 3 m) →
      (∀ a ∈ A, ∃ l ∈ L, ∀ u ∈ commSub (fixV (pCoreOf 2 (L ⊔ A))) L, a u = l u) →
      commV L = commSub (fixV (pCoreOf 2 (L ⊔ A))) L

end FFC

end CFSG.Quasithin
