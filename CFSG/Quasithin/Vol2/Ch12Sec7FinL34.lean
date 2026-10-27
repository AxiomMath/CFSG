module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch12Sec7Final

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127

@[expose] def Final1271L34Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G), Setting1274 G T L V t z →
    ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
      H ≤ Subgroup.centralizer ({z} : Set G) →
      IsPSL 3 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) →
      L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G) →
      ∀ g : G, conjSubgroup V g ≤ T ⊓ Subgroup.centralizer (V : Set G) →
        ¬ conjSubgroup V g ≤ pCoreOf 2 H →
        ∃ (g' : G) (H₁ : Subgroup G), H₁ ≤ H ∧ conjSubgroup V g' ≤ T ∧
          conjSubgroup V g' ≤ H₁ ∧ IsSylowIn 2 (T ⊓ H₁) H₁ ∧
          E1.tauOf H T (conjSubgroup V g') ≤ H₁ ∧
          IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))) ∧
          ¬ conjSubgroup V g' ≤ pCoreOf 2 H₁

end CFSG.Quasithin.H13
