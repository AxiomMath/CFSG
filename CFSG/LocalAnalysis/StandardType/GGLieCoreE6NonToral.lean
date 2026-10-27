module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.PerfectCentralQuotient

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open scoped commutatorElement

@[expose] def GGLieE6NonToralNoA8 :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    (letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) →
    ∀ A : Subgroup (ModGL Tag.E6 L),
    A ≤ adjointGroup Tag.E6 L → IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
    ¬ IsToralSubgroup Tag.E6 L A →
    ∀ J : Subgroup (ModGL Tag.E6 L), J ≤ adjointGroup Tag.E6 L →
      J ≤ Subgroup.centralizer (A : Set (ModGL Tag.E6 L)) →
      ⁅J, J⁆ = J → ¬ LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 1

end CFSG.StandardType.LieCore
