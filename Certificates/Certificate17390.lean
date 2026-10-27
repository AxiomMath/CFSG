module

public import CFSG.Sporadic.Schreier.ONOuterDefs
public import CFSG.RankThree.Native.ONSevenData
import Certificates.Kernel.ONSeven.C17390
import Certificates.Kernel.ONSeven.G17390Sound

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSpor.ONS in
theorem certificate17390 : 
    Subgroup.closure {g | ∃ r : Fin 3,
      g ∈ CFSG.ONSchreier.evalList CFSG.RankThree.Native.onSevenCentWords[(r : ℕ)]!} =
      CFSG.ONSchreier.Pv :=
  closure_cent_eq_Pv (by decide) (by decide) ch17390_0 ch17390_1 ch17390_2

end Certificates
