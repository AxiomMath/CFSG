module

public import Certificates.Certificate745103

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutE8L33

open CFSG.GH74.KGroups CFSG.GroupTheory


theorem e8GenFacts_QA : E8GenFacts ↥L33.QA.originalSubgroup :=
  Certificates.certificate745103.1

theorem not_eight_le_card_of_le_QP (B : Subgroup (Equiv.Perm (Fin 26)))
    (hB : B ≤ L33.QP.originalSubgroup) (h2 : ∀ b ∈ B, b ^ 2 = 1) : ¬ 8 ≤ Nat.card B :=
  Certificates.certificate745103.2 B hB h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutE8L33
