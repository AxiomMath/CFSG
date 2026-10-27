module

public import Certificates.Kernel.Co1ThreeK.DataZ
public import Certificates.Kernel.Co1ThreeK.DataP
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1Three.Slp
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.TabCo1ThreeB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1B CFSG.KC.Co1Cl CFSG.KS.SporSch.M24

theorem kKZ : dagWK KZ.M KZ.MI 2 91 CZ.KW = true := by quickRfl

theorem kZB : (Nat.beq (KZ.M 0) (L.M 9) && Nat.beq (KZ.M 1) (L.M 10)) = true := by quickRfl

theorem kZW : CZ.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++
      CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext := by decide +kernel

theorem kZ : (Nat.blt CZ.V 729 && Nat.beq (mulWK (KZ.M 90) (KD.M 87))
    (mulWK (KD.M 87) (epK L.M 3 [0, 1, 2, 3, 4, 5] CZ.V oneK))) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
