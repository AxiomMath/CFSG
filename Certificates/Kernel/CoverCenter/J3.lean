module

public import Certificates.Data.Kernel.CoverCK
public import Certificates.Data.CoverCenterThreeJ3
public import Certificates.Kernel.LocalComp.J3Seeds
public import Certificates.Kernel.CoverCenter.Masks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCover.J3

open CFSG.KC.CoverCK CFSG.SectionRank.Native CertificateChecks.KernelLC.J3Ops

theorem cover_K : coverK2 80 SA.M SB.M j3CoverData = true := by decide +kernel

theorem orbit_K : coverOrbitK2 80 SA.M SB.M j3CoverData 2 0 CFSG.KD.CoverMasks.J3.c0 = true := by
  decide +kernel

end CertificateChecks.KernelCover.J3

end
