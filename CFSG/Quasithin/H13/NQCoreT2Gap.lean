module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.NQSetupDefs

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

@[expose] def StmtEscapingPairExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    (∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M) →
    normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M →
    ∀ H₀ H : Subgroup G, quasithinIsMaxTwoLocal H₀ → T ≤ H₀ → T ≤ H → H ≤ H₀ → ¬ H ≤ M →
      (∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K) →
      IsSimpleGroup ↥((CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤)))

@[expose] def StmtEscapingSingleTwoRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    (∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M) →
    normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M →
    ∀ H₀ H : Subgroup G, quasithinIsMaxTwoLocal H₀ → T ≤ H₀ → T ≤ H → H ≤ H₀ → ¬ H ≤ M →
      (∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K) →
      IsSimpleGroup ↥((CFSG.perfectResidual ↥H).map
        (QuotientGroup.mk' (kerIn ((H ⊓ M).subgroupOf H) ⊤))) →
      kerIn ((H ⊓ M).subgroupOf H) ⊤ = CFSG.Open.pCore 2 ↥H →
      (Nonempty (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
          CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype) ≃*
            alternatingGroup (Fin 5)) ∨
        CFSG.Blueprint.LieModel (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
          CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) .PSL 3 2 1 ∨
        CFSG.Blueprint.LieModel (↥((CFSG.perfectResidual ↥H).map H.subtype) ⧸
          CFSG.pCore 2 ↥((CFSG.perfectResidual ↥H).map H.subtype)) .PSU 3 3 1) →
      CFSG.pRank 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤ 2

end CFSG.Quasithin.H13.NQCore
