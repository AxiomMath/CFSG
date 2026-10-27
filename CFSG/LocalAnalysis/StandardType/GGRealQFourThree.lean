module

public import CFSG.LocalAnalysis.StandardType.GGRealQFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

@[expose] def GGReflRealizedQFourInputThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 3 →
      ∀ X : Subgroup G, (X = L ∨ ∃ y, GGNbr p B x D J y X) →
        GGInnerDiagOnLabel GGLabQFour p Bs X → GGReflRealizedIn p Bs X

end CFSG.StandardType

end
