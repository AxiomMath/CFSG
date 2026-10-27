module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.H13.A6S4Defs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace L32Hat

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] def HatHyp (S : Setting4 G T L V) (H : Subgroup G) : Prop :=
  oTwoRes (solvRad H) ≠ ⊥ ∧
    (pCoreOf 2 H).relIndex (pCoreOf 2 (S.L1 ⊔ T)) ≤ 4 ∧
    4 ≤ mIdx (conjClosure S.V3 H)
      (centralizerMod (fsuV1 T V) (conjClosure S.V3 H) (pCoreOf 2 (S.L1 ⊔ T)))

end L32Hat

end CFSG.Quasithin.H13.A6
