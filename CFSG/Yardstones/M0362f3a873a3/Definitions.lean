module

public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.OddStandard.ResidualOddLie
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Yardstones.M0362f3a873a3

@[expose] def SmallF3LieQuotient (Q : Type) [Group Q] : Prop :=
  CFSG.Blueprint.LieModel Q .PSL 3 3 1 ∨ CFSG.Blueprint.LieModel Q .PSU 3 3 1 ∨
    CFSG.Blueprint.LieModel Q .PSp 2 3 1 ∨ CFSG.Blueprint.LieModel Q .PSL 4 3 1 ∨
    CFSG.Blueprint.LieModel Q .PSU 4 3 1 ∨ CFSG.Blueprint.LieModel Q .POmegaOdd 3 3 1 ∨
    CFSG.Blueprint.LieModel Q .POmegaPlus 4 3 1 ∨ CFSG.Blueprint.LieModel Q .POmegaMinus 4 3 1

@[expose] def SmallF3StandardOddLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
      SmallF3LieQuotient (L ⧸ Subgroup.center L) → CFSG.Blueprint.OddLieType G

@[expose] def SmallF3StandardOddLieU : Prop :=
  CFSG.OddStandard.SmallF3Interfaces.SmallF3StandardOddLieU

@[expose] def L2OrReeLieQuotient (Q : Type) [Group Q] : Prop :=
  (∃ p f : ℕ, CFSG.Blueprint.LieModel Q .PSL 2 p f) ∨
    ∃ f : ℕ, CFSG.Blueprint.LieModel Q .twistedG2 0 3 f

@[expose] def OddLieThm187bResidualL2Ree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.OddStandard.StandardSetting G L →
    ((∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) →
      CFSG.ComponentClassification.OutcomeLocal.UOutcome G) →
    CFSG.Blueprint.OddLieType (L ⧸ Subgroup.center L) →
    L2OrReeLieQuotient (L ⧸ Subgroup.center L) →
    ¬ Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 6)) →
    ¬ CFSG.OddStandard.HarrisSolomonFritzScope L →
    (Odd (Nat.card (Subgroup.center L)) ∨
      ∃ p n r : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ 0 < r ∧
        (CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL (2 * n) p r ∨
          CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU (2 * n) p r) ∧
        ordProj[2] (Nat.card (Subgroup.center L)) ≠
          ordProj[2] (Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ Subgroup.center L)))) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
      CFSG.OddStandard.AltOutcome G ∨ CFSG.Blueprint.OddLieType G ∨
        (CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .HS)

@[expose] def OddLieThm187bResidualHigherRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.OddStandard.StandardSetting G L →
    ((∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) →
      CFSG.ComponentClassification.OutcomeLocal.UOutcome G) →
    CFSG.Blueprint.OddLieType (L ⧸ Subgroup.center L) →
    ¬ SmallF3LieQuotient (L ⧸ Subgroup.center L) →
    ¬ L2OrReeLieQuotient (L ⧸ Subgroup.center L) →
    ¬ Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 6)) →
    ¬ CFSG.OddStandard.HarrisSolomonFritzScope L →
    (Odd (Nat.card (Subgroup.center L)) ∨
      ∃ p n r : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ 0 < r ∧
        (CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL (2 * n) p r ∨
          CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU (2 * n) p r) ∧
        ordProj[2] (Nat.card (Subgroup.center L)) ≠
          ordProj[2] (Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ Subgroup.center L)))) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
      CFSG.OddStandard.AltOutcome G ∨ CFSG.Blueprint.OddLieType G ∨
        (CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .HS)

end CFSG.Yardstones.M0362f3a873a3
