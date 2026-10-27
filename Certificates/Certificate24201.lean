module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.OrbitData
import Certificates.Kernel.ThBfs.OrbGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate24201 : CFSG.EvenSporadicStandard.ThStd.LocalDataTh.orbitList.length = 22680 :=
  KernelThBfs.orbitList_length

end Certificates
