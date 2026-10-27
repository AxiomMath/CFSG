module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCardInputs
import Certificates.Kernel.Misc.Coset.C3090

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.EvenSmallLie.SympSix.Co3Ident in
theorem certificate3090 : ((genSub {r | r ∈ relsV.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).FiniteIndex ∧
      (genSub {r | r ∈ relsV.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).index ≤ 170775)
    ∧ ((genSub {r | r ∈ relsV1.map FreeGroup.mk} (subsetOf _ [0, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub {r | r ∈ relsV1.map FreeGroup.mk} (subsetOf _ [0, 2, 3, 4, 5])).index ≤ 7560)
    ∧ (Finite (PG _ relsV2) ∧ Nat.card (PG _ relsV2) ≤ 384)
    ∧ ((genSub {r | r ∈ relsVw.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).FiniteIndex ∧
      (genSub {r | r ∈ relsVw.map FreeGroup.mk} (subsetOf 7 [0, 1, 2, 4, 5, 6])).index ≤ 1) :=
  ⟨KernelMiscCoset.C3090.v0, KernelMiscCoset.C3090.v1, KernelMiscCoset.C3090.v2,
    KernelMiscCoset.C3090.vw⟩

end Certificates
