module

public import Certificates.Kernel.Co1ThreeK.DataMoore
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Data.Kernel.Co1Three.Moore
public import Certificates.Data.TabCo1ThreeMoore
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KS.SporSch.M24 CFSG.KC.Co1Moore

theorem kKM : dagWK KM.M KM.MI 2 94 CM.KW = true := by quickRfl

theorem kMB : (Nat.beq (KM.M 0) (CertificateChecks.KernelCo1B.Cent2045.D1.M 0) &&
    Nat.beq (KM.M 1) (CertificateChecks.KernelCo1B.Cent2045.D1.M 1)) = true := by quickRfl

theorem kMW : CM.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++
      CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeMoore.ext := by decide +kernel

theorem kM : mooreK (fun j => ndK KM.M 94 (87 + j)) (R.M 2) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
