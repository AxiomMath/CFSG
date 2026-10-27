module

public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def D310L34Fact : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (M K T I : Subgroup Γ),
    SQTKGroup ↥M → IsSylowTwoOf T M → K ≤ M → M ≤ Subgroup.normalizer (K : Set Γ) →
    M = K ⊔ T → IsIrrPlusIn K (conjClosure I T) T I →
    ∀ hVT : IsElemAbelian 2 (conjClosure I T),
      pCoreOf 2 (autOn M (conjClosure I T)) = ⊥ →
      LieModel ↥(autOn K (conjClosure I T)) .PSL 3 2 2 →
      qhatInt M (conjClosure I T) hVT ≤ 2 → I = conjClosure I T

@[expose] def B45L34Fact : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (U Y K T Cg : Subgroup Γ) [IsMulCommutative ↥U],
    InternalSec.ISec U Y K Cg → SQTKGroup ↥(autOn K U) → LieModel ↥(autOn K U) .PSL 3 2 2 →
    T ≤ Y → IsSylowTwoOf T Y → Y = K ⊔ T → E2.IsDiagramNontrivial T K (T ⊓ K) →
      (2 : WithTop ℚ) < qhatOf (autSec (autOn Y U) ⊤ (Cg.subgroupOf U))

end CFSG.Quasithin.H13
