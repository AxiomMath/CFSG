module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.GroupTheory.E8GenFacts
import Certificates.Kernel.E8K.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate745103 : CFSG.GroupTheory.E8GenFacts ↥CFSG.GH74.KGroups.L33.QA.originalSubgroup ∧
    ∀ B : Subgroup (Equiv.Perm (Fin 26)), B ≤ CFSG.GH74.KGroups.L33.QP.originalSubgroup →
      (∀ b ∈ B, b ^ 2 = 1) → ¬ 8 ≤ Nat.card B := KernelE8K.Glue.l33

end Certificates
