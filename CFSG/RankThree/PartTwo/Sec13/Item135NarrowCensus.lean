module

import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (isoLThreePi_of_mulEquiv)
open scoped MatrixGroups

@[expose] def Item4_4Types135 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → Group.IsPerfect G →
    ∀ (K : Subgroup G) [K.Normal], Group.IsSolvable K → IsSimpleGroup (G ⧸ K) →
      (IsLThreePi (G ⧸ K) ∨ Nonempty (G ⧸ K ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
        Nonempty (G ⧸ K ≃* CFSG.Blueprint.NativeSporadic.J2)) →
      IsQuasisimple (G ⧸ CFSG.pCore 2 G) ∨
      Nonempty (G ⧸ Sec4.oTwoFitting G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧
        Nonempty (G ⧸ Sec4.oTwoP p G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ∨
      (Nonempty (G ⧸ Sec4.oTwoP 3 G ≃* projSL 3 (GaloisField 3 1)) ∨
        Sec4.IsExtOf (G ⧸ Sec4.oTwoP 3 G) (alternatingGroup (Fin 5)) Sec4.Q8D8) ∨
      (CFSG.pCore 2 G = ⊥ ∧ (¬ 3 ∣ Nat.card K →
        (CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 2 ∧
            (IsQuasisimple (G ⧸ CFSG.oddCore G) ∨
              Sec4.IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 5)) Sec4.Q8D8)) ∨
          (CFSG.Open.pRank 2 (⊤ : Subgroup G) = 3 ∧
            (Sec4.IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 5)) Sec4.Q8D8 ∨
              Sec4.IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 5)) Sec4.Z4Q8Q8 ∨
              Sec4.IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 6)) Sec4.Z4Q8Q8))))

theorem item4_4Types135_of_item4_4 (h44 : Sec4.Item4_4) : Item4_4Types135 :=
  fun G _ _ hG hperf K _ hK hsimple _ => h44 G hG hperf K hK hsimple

end CFSG.RankThree.PartTwo.Sec13
