module

public import Certificates.Kernel.Census.M24C.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW3
public import CFSG.Certificates.Kernel.Census.ToMain
import all Certificates.Kernel.Census.M24C.Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW3
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW2
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicWitData
import all CFSG.RankThree.Native.PermEnumeration
import all CFSG.Monster.Code.Defs
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

namespace CertificateChecks.KernelCensus.M24C

open CFSG.KC.Census CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.RankTwoSporadic.M22
open CFSG.ComponentClassification.RankTwoSporadic.M24

set_option maxRecDepth 1000000

@[expose] noncomputable def clE : ClosW := ⟨e0cl.1, e0cl.2.1, e0cl.2.2.1, e0cl.2.2.2⟩

theorem kE0e : enumOKK 24 (e0.map (unpackP 24 5)) m22PS (maskCert 24 (e0.map (unpackP 24 5))) =
    true := by
  decide +kernel

theorem kE0w : witOKW3 24 m22PS (inXL 24 (Xs.map (unpackP 24 5))) allA false false true
    (e0.map (unpackP 24 5)) (maskCert 24 (e0.map (unpackP 24 5))) #[] default clE
    (e0wit.toMain 24 5) = true := by
  decide +kernel

end CertificateChecks.KernelCensus.M24C

end
