module

public import Certificates.Data.SmithB45ExcRuData
import Certificates.Kernel.B45.C260392K
import Certificates.Data.Kernel.B45Perm.Defs
import Certificates.Data.SmithB45ExcHSData
import Certificates.Kernel.LocalQT.SV.C4126T
import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.B45PermSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

namespace CertificateChecks.Batch260392

open CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.KC.B45P CFSG.Quasithin.B45Exc.Ru CFSG.Quasithin.B45Exc.Tab
  CFSG.QuasithinUnique.Bridge.RuExcl CertificateChecks.KernelSporSch.RuG

theorem a0P : ruA0P = (unpack 4060 12 A0, unpack 4060 12 A0I) := by
  unfold ruA0P
  rw [(inv_of a0_eq pA0).1, a0_eq]

theorem gens_eq : [ruA0P, ruA1P] = unpackP 4060 12 [A0, A1] [A0I, A1I] := by
  unfold ruA0P ruA1P
  rw [(inv_of a0_eq pA0).1, (inv_of a1_eq pA1).1, a0_eq, a1_eq]
  rfl

theorem ru_b29 : ruB29Check = true := by
  unfold ruB29Check ruGens
  rw [gens_eq, a0P]
  exact b45OrdK_sound CFSG.KD.B45.C260392.b29K

end CertificateChecks.Batch260392

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Exc.Ru in
theorem certificate260392 : ruB29Check = true :=
  CertificateChecks.Batch260392.ru_b29

end Certificates
