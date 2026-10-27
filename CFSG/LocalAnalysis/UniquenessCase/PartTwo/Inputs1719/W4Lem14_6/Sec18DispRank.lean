module

public import CFSG.Quasithin.Background.SmithD37Lin
public import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.Quasithin.Background.F6CatSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem rkIdx_fixV_zpowers_eq_dispRank
    {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1) (t : MulAut U) :
    letI : Module (ZMod 2) (Additive U) := CFSG.Quasithin.SmithD37.zmodModule hU
    rkIdx (fixV (Subgroup.zpowers t)) =
      CFSG.QuasithinUnique.Setup.X7b.dispRank
        (CFSG.Quasithin.SmithD37.autLin hU t) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive U) := CFSG.Quasithin.SmithD37.zmodModule hU
  rw [rkIdx, CFSG.Quasithin.B45Sz.index_fixV_zpowers_eq CFSG.Quasithin.SmithD37.theta t,
    padicValNat.prime_pow]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
