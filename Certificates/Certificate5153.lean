module

public import Certificates.Data.GH74J2CentCheck
public meta import Certificates.Data.GH74J2CentCheck
import Certificates.Kernel.GH74.J2CentJ
import Certificates.Kernel.GH74.J2CentE
import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.GH74.Generic.S45.LEvSporGen
import CFSG.LocalAnalysis.SectionRank.PRank
import Certificates.Kernel.GH74.Derived
import Certificates.Kernel.GH74.J2Cent5

public section

namespace Certificates

open CertificateChecks

theorem certificate5153 :
    CFSG.GH74.Generic.S45.EvSpor.j2EEnumOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2ENormalOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2EStructOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2ECentOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2OrbitOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2PerfectOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2SylowOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2AutCount ≤ 1920 :=
  ⟨KernelGH74.J2CentE.eEnum_ok, KernelGH74.J2CentE.eNormal_ok, KernelGH74.J2CentE.eStruct_ok,
    KernelGH74.J2CentE.eCent_ok, KernelGH74.J2CentE.orbit_ok, KernelGH74.J2CentE.perfect_ok,
    KernelGH74.J2CentE.sylow_ok, KernelGH74.J2CentE.autCount_le⟩

end Certificates
