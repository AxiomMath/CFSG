module

public import Certificates.Data.CFSGNative.MonsterB.PacketCheck
import Certificates.Kernel.MonsterB.Packet3050

public section

open CFSG.Monster.B.Rep4371 CertificateChecks.KernelBM.Pkt3050

namespace Certificates

open CFSG.Monster.B.Rep4371 in
theorem certificate3050 : (((List.range 23).all fun i => Native.genCheck i) = true)
    ∧ (((List.range 12).all fun i => Native.genCheck (23 + i)) = true)
    ∧ (((List.range 11).all fun i => Native.genCheck (35 + i)) = true)
    ∧ (Native.genCheck 46 = true)
    ∧ (Native.tauCheck = true)
    ∧ (Native.labelsCheck = true ∧ Native.spinIndexCheck = true)
    ∧ (Native.octDataOK = true ∧ Native.octSignOK = true) :=
  ⟨List.all_eq_true.2 fun _ hi => genCheck_pauli (List.mem_range.1 hi),
    List.all_eq_true.2 fun _ hi => genCheck_perm (List.mem_range.1 hi),
    List.all_eq_true.2 fun _ hi => genCheck_sign (List.mem_range.1 hi),
    genCheck_xi, tauCheck_true, labels_ok, oct_ok⟩

end Certificates
