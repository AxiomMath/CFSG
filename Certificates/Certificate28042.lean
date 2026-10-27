module

public import Certificates.Data.Kernel.EvenBN.Thm49EF6
import Certificates.Kernel.EvenBN.Thm49EF6

public section

namespace Certificates

open CertificateChecks

theorem certificate28042 : ∃ W : CFSG.KD.T49.F6W, CFSG.KD.T49.F6OK W :=
  ⟨KernelT49.w42, fun _ hj => KernelSpor.Tits2264.gen_eq hj,
    fun _ hj => KernelMisc.TitsText.titsDerivedArrs_get (by omega),
    KernelSporSch.TitsCommon.z_eq, KernelT49.f6K_w42⟩

end Certificates
