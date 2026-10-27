module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE6DepPerpTableRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGE6DepPerpCfg p Bs L K →
          ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
            ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
              GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labK (K' ⧸ Subgroup.center K') →
                GGTablePRow p labJ labK → GGE6DepPerpCfg p Bs L K'

end CFSG.StandardType

end
