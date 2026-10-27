module

public import Certificates.Data.CoverBRealJ3
public import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Certificates.Kernel.OpsRealSound
import CFSG.Certificates.Kernel.OpsKSound
import Certificates.Kernel.Real.J3
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.Native CFSG.KC.OpsK CertificateChecks.KernelJ3L

open CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.Native in
theorem certificate7264 : RealData.checkElem (ops2 80) j3Real = true := by
  have jA : (ops2 80).decode CFSG.Blueprint.NativeSporadic.J3Seed1 =
      (hom2 80 (by norm_num)).U JA.M := by
    rw [JA.eq]
    exact CFSG.KC.Co1F2.bind_sound JA.bind
  have jB : (ops2 80).decode CFSG.Blueprint.NativeSporadic.J3Seed2 =
      (hom2 80 (by norm_num)).U JB.M := by
    rw [JB.eq]
    exact CFSG.KC.Co1F2.bind_sound JB.bind
  exact CFSG.KC.OpsReal.checkElem_of_N (hom2 80 (by norm_num)) (D := j3Real)
    ((congrArg (ops2 80).decode
      (rfl : j3Real.base.seedA = CFSG.Blueprint.NativeSporadic.J3Seed1)).trans jA)
    ((congrArg (ops2 80).decode
      (rfl : j3Real.base.seedB = CFSG.Blueprint.NativeSporadic.J3Seed2)).trans jB)
    trivial trivial KernelReal.J3.real_K

end Certificates
