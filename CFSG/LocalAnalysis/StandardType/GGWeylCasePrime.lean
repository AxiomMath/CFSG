module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGSecFiveWeylCase' {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Prop :=
  ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs)

@[expose] def GGScalarsOrWeyl' {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Prop :=
  GGScalarsPmOne Bs ∨ GGSecFiveWeylCase' p B Bs x D J

end CFSG.StandardType

end
