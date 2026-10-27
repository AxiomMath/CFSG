module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def F112L2FourChiefFactC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    F112ListA L1 L2 S → ∀ Li : Subgroup G, (Li = L1 ∨ Li = L2) → IsL2Quot 2 (oTwoQuot ↥Li) →
      ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (Li : Set G) →
        ∀ n : ℕ, IsChiefSeriesFrom Li (pCoreOf 2 Li) (pCoreOf 2 Li) n → n ≤ 2

end CFSG.Quasithin.H13
