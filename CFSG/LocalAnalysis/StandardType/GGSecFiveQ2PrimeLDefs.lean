module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.Blueprint

@[expose] def GGSecFiveQ2PrimeLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 → Nat.card Bs = 3 ^ 6 →
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 →
      GGSecFiveWeylAt 3 B Bs x L D J (CoxeterMatrix.A 6) →
      GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) →
      Odd (Nat.card (Subgroup.center ↥L))

end CFSG.StandardType
