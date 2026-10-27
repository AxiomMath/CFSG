module

public import Certificates.Kernel.Co1ThreeK.DataCensus
public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Data.Kernel.Co1Three.Census
public import Certificates.Data.TabCo1Census
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1Moore CFSG.KC.Co1Census
  CFSG.HardMathSupport.Dickson.I271.TabCo1

theorem kKC : dagWK KC.M KC.MI 2 90 CC.KW = true := by quickRfl

theorem kCB : (Nat.beq (KC.M 0) (CertificateChecks.KernelCo1B.Cent2045.D1.M 0) &&
    Nat.beq (KC.M 1) (CertificateChecks.KernelCo1B.Cent2045.D1.M 1)) = true := by quickRfl

theorem kCW : CC.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    chainDerivs () ++ CFSG.HardMathSupport.Dickson.I271.TabCo1Census.ext := by decide +kernel

theorem kKG : dagWK KG.M KG.MI 2 KG.N Timmesfeld.Co1Five.dagWords = true := by quickRfl

theorem kGB : (Nat.beq (KG.M 0) (CertificateChecks.KernelCo1B.Cent2045.D1.M 0) &&
    Nat.beq (KG.M 1) (CertificateChecks.KernelCo1B.Cent2045.D1.M 1)) = true := by quickRfl

theorem kP0 : bindListK 24 24 CC.P0 repD0.toList = true := by quickRfl
theorem kP1 : bindListK 24 24 CC.P1 repD1.toList = true := by quickRfl
theorem kPZ : bindListK 24 24 CC.PZ repZ.toList = true := by quickRfl

theorem kC : censusK (ndK KC.M 90) (ndK KC.MI 90)
    (a0K (getK KG.M KG.N (Timmesfeld.Co1Five.idxD.getD 0 0))
      (getK KG.M KG.N (Timmesfeld.Co1Five.idxD.getD 1 0))
      (getK KG.M KG.N (Timmesfeld.Co1Five.idxD.getD 2 0)))
    CC.P0 CC.P1 CC.PZ CFSG.HardMathSupport.Dickson.I271.TabCo1Census.steps = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
