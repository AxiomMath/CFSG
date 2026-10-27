module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)

@[expose] def Step3_3_13Bender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D → InH T H →
    Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    (∃ n : ℕ, Even n ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 2 n) →
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

end CFSG.Quasithin.H13
