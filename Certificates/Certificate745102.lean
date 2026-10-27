module

public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.GroupTheory.E8GenFacts
import Certificates.Kernel.E8K.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate745102 : CFSG.GroupTheory.E8GenFacts ↥CFSG.GH74.KGroups.U33.QA.originalSubgroup ∧
    ∀ B : Subgroup (Equiv.Perm (Fin 28)), B ≤ CFSG.GH74.KGroups.U33.QP.originalSubgroup →
      (∀ b ∈ B, b ^ 2 = 1) → ¬ 8 ≤ Nat.card B := KernelE8K.Glue.u33

end Certificates
