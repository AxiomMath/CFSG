module

public import Certificates.Certificate745102
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutE8U33

open CFSG.GH74.KGroups CFSG.GroupTheory


theorem e8GenFacts_QA : E8GenFacts ↥U33.QA.originalSubgroup :=
  Certificates.certificate745102.1

theorem not_eight_le_card_of_le_QP (B : Subgroup (Equiv.Perm (Fin 28)))
    (hB : B ≤ U33.QP.originalSubgroup) (h2 : ∀ b ∈ B, b ^ 2 = 1) : ¬ 8 ≤ Nat.card B :=
  Certificates.certificate745102.2 B hB h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutE8U33
