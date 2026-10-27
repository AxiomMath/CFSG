module

public import CFSG.LieType.Multipliers.G23Data
public import CFSG.Sporadic.He.FpSpec
import Certificates.Kernel.Misc.Coset.C12042

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.G23 CFSG.CosetTable CFSG.Sporadic.He.Native in
theorem certificate12042 :
    (toMat 3 14 aArr * toMat 3 14 aArr = 1 ∧ toMat 3 14 bArr * toMat 3 14 bInvArr = 1 ∧
      (∀ r ∈ rels, toMat 3 14 (wordArr r) = 1) ∧
      (∀ j, toMat 3 14 (wordArr (genWord j)) = rootMat j) ∧
      ∀ i, toMat 3 14 (wordArr (commWords (CFSG.LieType.Multipliers.G23.pairs i))) = toMat 3 14 (letterArr (i, true)))
    ∧ (Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 4245696) :=
  ⟨KernelMiscCoset.C12042.model_facts, KernelMiscCoset.C12042.card_le⟩

end Certificates
