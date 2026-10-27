module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
public import Certificates.Certificate16949
import Certificates.Kernel.ThFive.Glue

public section

namespace Certificates

theorem certificate1023505 :     CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Th :=
  by
    intros
    exact @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv ↥CFSG.Sporadic.Th.J
      CFSG.Blueprint.NativeSporadic.Th inferInstance inferInstance CFSG.Sporadic.Th.thEquivJ.symm 5
      CertificateChecks.KernelThFive.sporKRest_cover_Th_5_kernel

end Certificates
