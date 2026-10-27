module

public import Certificates.Kernel.Co3Pair.Text
public import Certificates.Kernel.Co3Pair.EnumA
public import Certificates.Kernel.Co3Pair.EnumB
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Pair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def EA.SK : List Nat := (List.range 1215).map EA.SKT

@[expose] noncomputable def EB.SK : List Nat := (List.range 14580).map EB.SKT

theorem kPerm : allN 6 (fun k => permB 276 9 (PTN.L k)) = true := by quickRfl

theorem kEA : (Nat.beq EA.ng 2 && Nat.beq EA.N 1215 &&
    allN 2 (fun k => Nat.beq (EA.G k) (PTN.L (2 + k)))) = true := by quickRfl

theorem kEB : (Nat.beq EB.ng 2 && Nat.beq EB.N 14580 &&
    allN 2 (fun k => Nat.beq (EB.G k) (PTN.L (4 + k)))) = true := by quickRfl

theorem kEAkeys : CFSG.KC.BfsPin.keysSK 276 9 CFSG.Sporadic.Schreier.Co3.co3ChainBaseArr.toList EA.N
    EA.T EA.SK = true := by quickRfl

theorem kEBkeys : CFSG.KC.BfsPin.keysSK 276 9 CFSG.Sporadic.Schreier.Co3.co3ChainBaseArr.toList EB.N
    EB.T EB.SK = true := by quickRfl

end CertificateChecks.KernelCo3Pair
