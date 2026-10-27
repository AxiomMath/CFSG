module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpResidual
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGForkA8TablePLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        (GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
          GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) →
        ∀ labJ labL : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labL →
          GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labL (L ⧸ Subgroup.center L) →
          GGTablePAt 7 (J ⧸ Subgroup.center J) (L ⧸ Subgroup.center L)

end CFSG.StandardType
