module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def D310L2Fact : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (M K T I : Subgroup Γ) (n : ℕ),
    SQTKGroup ↥M → IsSylowTwoOf T M → K ≤ M → M ≤ Subgroup.normalizer (K : Set Γ) →
    M = K ⊔ T → IsIrrPlusIn K (conjClosure I T) T I →
    ∀ hVT : IsElemAbelian 2 (conjClosure I T),
      pCoreOf 2 (autOn M (conjClosure I T)) = ⊥ →
      LieModel ↥(autOn K (conjClosure I T)) .PSL 2 2 n →
      qhatInt M (conjClosure I T) hVT ≤ 2 → I = conjClosure I T

end CFSG.Quasithin.H13
