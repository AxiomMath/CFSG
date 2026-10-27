module

public import Certificates.Kernel.Asch54.Co3Text
public import Certificates.Kernel.Asch54.Co3Chains
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAsch54.Co3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.LocalAnalysis.WeakClosure81.SporCo3
open CertificateChecks.KernelSpor CertificateChecks.KernelAsch54

@[expose] noncomputable def PQ (j : Nat) : Nat :=
  if j < 9 then ch75337a.S (8 + j) else ch75337b.S (j - 1)

@[expose] noncomputable def PQI (j : Nat) : Nat :=
  if j < 9 then ch75337a.SI (8 + j) else ch75337b.SI (j - 1)

@[expose] noncomputable def siftOne (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (276 * 9)) 0 && allN 276 (fun t => Nat.blt (pg 9 (mask 9) G t) 276) &&
    Co3C.sift G

theorem lnA : allN 9 (fun j => Nat.beq (ch75337a.S (8 + j)) (Co3PT.L (Nat.add 0 j))) = true := by
  quickRfl

theorem lnB : allN 10 (fun j => Nat.beq (ch75337b.S (8 + j)) (Co3PT.L (Nat.add 9 j))) = true := by
  quickRfl

theorem lnTA : allN 8 (fun j => Nat.beq (ch75337a.S j) (Co3Text.L (Nat.add 35 j))) = true := by
  quickRfl

theorem lnTB : allN 8 (fun j => Nat.beq (ch75337b.S j) (Co3Text.L (Nat.add 35 j))) = true := by
  quickRfl

theorem permQ : allN 19 (fun j => permOK 276 9 (mask 9) (276 * 9) (PQ j) (PQI j)) = true := by
  quickRfl

theorem siftQ : allN 19 (fun j => siftOne (PQ j)) = true := by
  quickRfl

theorem wordA0 : wordEqK 276 9 (mask 9) (pidn 276 9) PQ PQI 19 pairWordA0 (Co3C.S 0) = true := by
  quickRfl

theorem wordA1 : wordEqK 276 9 (mask 9) (pidn 276 9) PQ PQI 19 pairWordA1 (Co3C.S 1) = true := by
  quickRfl

theorem bgetA : allN 10 (fun t => Nat.beq (#[0, 227, 154, 106, 1, 2, 3, 4, 5, 6] : Array Nat)[t]!
    (pg 9 (mask 9) ch75337a.BP t)) = true := by
  quickRfl

theorem bgetB : allN 11 (fun t => Nat.beq (#[0, 106, 200, 28, 55, 1, 2, 3, 4, 5, 6] : Array Nat)[t]!
    (pg 9 (mask 9) ch75337b.BP t)) = true := by
  quickRfl

theorem orbA : (List.range 10).map (fun i => rcnt (ch75337a.LR i)) =
    [128, 4, 3, 2, 1, 1, 1, 1, 1, 1] := by
  decide +kernel

theorem orbB : (List.range 11).map (fun i => rcnt (ch75337b.LR i)) =
    [192, 3, 2, 6, 4, 1, 1, 1, 1, 1, 1] := by
  decide +kernel

end CertificateChecks.KernelAsch54.Co3

end
