module

public import CFSG.LieType.Multipliers.U42Data
import Certificates.Kernel.Misc.Coset.C10011
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Certificate113

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Bridge.TwoGen.Native CFSG.LieType.Multipliers.U42 CFSG.CosetTable in
theorem certificate10011 :
    (relCheck 45 (tauTab 0) (tauTab 0) (seqTab bIdx) (seqTab bIdx.reverse) checkWords = true)
    ∧ (Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 25920) :=
  ⟨CFSG.KS.Rel.relK_sound KernelMiscCoset.C10011.relK_eq, KernelMiscCoset.C10011.card_le⟩

end Certificates
