module

public import Certificates.Kernel.Co1ThreeK.DataP
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1Three.Slp
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.KS.SporSch.M24
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

@[expose] noncomputable def TS (k : Nat) : Nat := CFSG.KC.Co1F2.getL (nat_lit 0) CS.T k

@[expose] def EG : List (List Nat) := [[0, 1, 2, 3, 4, 5]]

@[expose] noncomputable def NZ : List (Nat × List Nat) := List.zip [6, 7, 8, 9, 10] CS.NR

@[expose] noncomputable def NT : List (Nat × List Nat) :=
  List.zip ((List.range 27).map (Nat.add 12)) CS.TR

theorem kSeeds : (Nat.beq CS.T.length 39 && allN 9 (fun k => Nat.beq (TS k) (L.M k)) &&
    lettersK 75 (Data.qGenWords.getD 6 []) && lettersK 75 (Data.qGenWords.getD 7 []) &&
    Nat.beq (TS 9) (wordWK L.M L.MI (Data.qGenWords.getD 6 [])) &&
    Nat.beq (TS 10) (wordWK L.M L.MI (Data.qGenWords.getD 7 [])) &&
    Nat.beq (TS 11) oneK && Nat.beq oneK idM && canAllK TS 12) = true := by quickRfl

theorem kProg : (Nat.beq CS.W.length 27 && runK TS [9, 10, 11] 12 12 CS.W) = true := by quickRfl

theorem kRel : (Nat.beq CS.Q.length 54 && eqsK TS 3 EG CS.Q) = true := by quickRfl

theorem kNorm : (Nat.beq CS.NR.length 5 && normK TS 3 EG NZ) = true := by quickRfl

theorem kAct : (Nat.beq CS.TR.length 27 && normK TS 3 EG NT) = true := by quickRfl

theorem kDist : (decide CS.TR.Nodup && CS.TR.all (fun r => r.all fun c => Nat.blt c 729)) =
    true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
