module

public import Certificates.Data.CFSGNative.MonsterB.PacketData
import Certificates.Kernel.BabyMonster.PktShape

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B in
theorem certificate3051 : (Native.packetShapeOK = true)
    ∧ (Native.packetEntryCount = 259183) :=
  ⟨KernelBM.PktShape.packetShapeOK_true, KernelBM.PktShape.packetEntryCount_eq'⟩

end Certificates
