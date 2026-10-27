module

public import CFSG.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch3Sec3Sec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

@[expose] def Insp3_3_14B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G), Setup331 G T M L →
    ¬ T ≤ Subgroup.normalizer (L : Set G) → ∀ (_ : IsMulCommutative ↥(vPlus L T)),
    Case3_3_8_one T L → IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
    ∃ H₁ H₂ : Subgroup G, InH T H₁ ∧ InH T H₂ ∧
      Nonempty (↥H₁ ⧸ CFSG.pCore 2 ↥H₁ ≃* ↥wreathS3Z2) ∧
      Nonempty (↥H₂ ⧸ CFSG.pCore 2 ↥H₂ ≃* ↥wreathS3Z2) ∧ H₁ ⊔ H₂ = L ⊔ T

end CFSG.Quasithin.H13
