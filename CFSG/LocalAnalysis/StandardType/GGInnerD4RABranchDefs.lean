module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def RALinearBranch : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (lab : LargeEvenLabel) (β : MulAut R) (Jb : Subgroup R),
    Subgroup.center R = ⊥ → LargeEvenInLambda2 lab → lab.tag = .A → β ^ 3 = 1 →
    Y10GField.InnDiagKind R lab β → IsComponentOf Jb (ggAutFixedSubgroup β) →
    ∃ labC : LargeEvenLabel, LargeEvenInLambda2 labC ∧ S2MathAs51600.TypeALabel labC ∧
      GGHasLabel labC (↥Jb ⧸ Subgroup.center ↥Jb)

@[expose] def RAUnitaryBranch : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (lab : LargeEvenLabel) (β : MulAut R) (Jb : Subgroup R),
    Subgroup.center R = ⊥ → LargeEvenInLambda2 lab → lab.tag = .twA → β ^ 3 = 1 →
    Y10GField.InnDiagKind R lab β → IsComponentOf Jb (ggAutFixedSubgroup β) →
    ∃ labC : LargeEvenLabel, LargeEvenInLambda2 labC ∧ S2MathAs51600.TypeALabel labC ∧
      GGHasLabel labC (↥Jb ⧸ Subgroup.center ↥Jb)

end CFSG.StandardType.GGInnerD4RAParts

end
