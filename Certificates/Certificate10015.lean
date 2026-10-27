module

public import CFSG.LieType.Multipliers.U62BridgeInputs
import Certificates.Kernel.Misc.Coset.C10015

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.U62 CFSG.CosetTable in
theorem certificate10015 :
    (bridgeCheck = true)
    ∧ (Finite (PG 5 rels) ∧ Nat.card (PG 5 rels) ≤ 9196830720) :=
  ⟨KernelMiscCoset.C10015.bridge, KernelMiscCoset.C10015.card_le⟩

end Certificates
