module

public import Certificates.Kernel.MonsterB.Co2Perms

public section

open CFSG.Monster.B.Co2 CFSG.KC.Co2Mem CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3026

open CFSG.Monster.B.Co2 CFSG.KC.Co2Mem CertificateChecks.KernelMonB

theorem kSizes : (Native.genRecords ()).size = 24 ∧ Native.quotientBasis.size = 22 ∧
    (Native.pairWords ()).size = 2 := by
  decide +kernel

theorem kRecords : ∀ i < 24, ((Native.genRecords ())[i]!.matrix.size == 24 &&
    (Native.genRecords ())[i]!.quotientMatrix.size == 22 &&
      Native.recordWordOK (Native.genRecords ())[i]!) = true := by
  decide +kernel

theorem kWords : ∀ i < 2, ((Native.pairWords ())[i]!.all fun l => l != 0 &&
    decide (l.natAbs ≤ 24)) = true := by
  decide +kernel

theorem dataCheck_eq_true : Native.dataCheck = true := by
  have hdeg : Native.deg () = 2300 := rfl
  obtain ⟨h1, h2, h3⟩ := kSizes
  unfold Native.dataCheck
  simp only [Bool.and_eq_true, allLt_iff, beq_iff_eq, hdeg]
  refine ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, ?_⟩, ?_⟩, kWords⟩
  · intro i hi
    have := kRecords i hi
    simpa only [Bool.and_eq_true, beq_iff_eq] using this
  · intro i hi
    exact isInvA_invCand (permutations_perm hi).1 (permutations_perm hi).2
  · intro i hi
    exact isInvA_invCand (pairPerms_perm hi).1 (pairPerms_perm hi).2

end CertificateChecks.Batch3026

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2 in
theorem certificate3026 : Native.dataCheck = true := CertificateChecks.Batch3026.dataCheck_eq_true

end Certificates
