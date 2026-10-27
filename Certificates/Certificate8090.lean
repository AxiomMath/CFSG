module

public import Certificates.Data.RankThree46Odd.Ly
public import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Certificates.Kernel.OpsW4NSound
import Certificates.Kernel.Census.W4Ly
import Certificates.Kernel.MatCert.GlueLy
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Census CertificateChecks.KernelMC CertificateChecks.KernelSporSch

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8090 : W4Data.check (opsP 5 111) lyW3 = true :=
  CFSG.KC.OpsW4N.w4Check_of_N HL
    ((congrArg _ (rfl : lyW3.base.seedA = CFSG.Blueprint.NativeSporadic.LySeed1)).trans lyA)
    ((congrArg _ (rfl : lyW3.base.seedB = CFSG.Blueprint.NativeSporadic.LySeed2)).trans lyB)
    (vldL LyBS.vA) (vldL LyBS.vB) KernelCensus.W4Ly.ly_K

end Certificates
