module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Subgroup
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Open (StatedSU)

theorem exists_isL2_le_of_isL2_statedSU (F : Type) [Field F] [Finite F] (f m : ℕ)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hm : 2 ≤ m)
    (L : Subgroup (StatedSU 3 (2 ^ f) F)) (hL : IsL2 L m) :
    ∃ J : Subgroup (StatedSU 3 (2 ^ f) F), IsL2 J f ∧ L ≤ J := by
  obtain ⟨v, -, hLv, hJ⟩ :=
    CFSG.ClassicalGroups.UnitaryFlag.exists_nonisotropic_le_stabilizer_of_isL2
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hF) hf hm hL
  exact ⟨_, hJ, hLv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
