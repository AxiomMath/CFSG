module

public import CFSG.LieType.Multipliers.Sz8Matrix
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.LieType.Multipliers.Sz8BridgeInputs
import Certificates.Kernel.Misc.Coset.C10008

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 TauCeti CFSG.CosetTable in
theorem certificate10008 :
    (matCheck rels = true)
    ∧ (genCheck = true)
    ∧ (Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 29120) :=
  ⟨KernelMiscCoset.C10008.matCheck_rels, KernelMiscCoset.C10008.genCheck_eq_true,
    KernelMiscCoset.C10008.card_le⟩

end Certificates
