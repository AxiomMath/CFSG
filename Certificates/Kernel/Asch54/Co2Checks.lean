module

public import Certificates.Kernel.Asch54.Co2Text
public import Certificates.Kernel.Asch54.Co2Chains
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Kernel.SporSch.Co2M.ChainS
public import CFSG.Certificates.Kernel.Spor.SiftBKSound
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAsch54.Co2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.LocalAnalysis.WeakClosure81.SporCo2
open CertificateChecks.KernelAsch54 CertificateChecks.KernelSpor

@[expose] noncomputable def L (j : Nat) : Nat := Co2PT.L j

@[expose] noncomputable def LI (j : Nat) : Nat := pinvS 2300 12 (mask 12) (Co2PT.L j)

@[expose] noncomputable def inPK (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (2300 * 12)) 0 && allN 2300 (fun t => Nat.blt (pg 12 (mask 12) G t) 2300) &&
    siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI Co2A.BP 6 0 G

@[expose] noncomputable def inA (q : Nat) : Bool :=
  siftBK 2300 12 (mask 12) (2300 * 12) 7 ch75342a.S ch75342a.SI ch75342a.LR ch75342a.ST 6 7 0
    (baseImK 12 (mask 12) 7 q ch75342a.BP)

@[expose] noncomputable def inB (q : Nat) : Bool :=
  siftBK 2300 12 (mask 12) (2300 * 12) 7 ch75342b.S ch75342b.SI ch75342b.LR ch75342b.ST 5 7 0
    (baseImK 12 (mask 12) 7 q ch75342b.BP)

theorem permL : allN 29 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (L j) (LI j)) = true := by
  quickRfl

theorem inP : allN 29 (fun j => inPK (L j)) = true := by
  quickRfl

theorem memA : allN 14 (fun j => inA (L j)) = true := by
  quickRfl

theorem memB : allN 15 (fun j => inB (L (Nat.add 14 j))) = true := by
  quickRfl

theorem memSA : allN 15 (fun j => inA (KernelSporSch.Co2LS.S j)) = true := by
  quickRfl

theorem memSB : allN 15 (fun j => inB (KernelSporSch.Co2LS.S j)) = true := by
  quickRfl

theorem wordA0 : wordEqK 2300 12 (mask 12) (pidn 2300 12) L LI 29 pairWordA0 (Co2A.S 0) = true := by
  quickRfl

theorem wordA1 : wordEqK 2300 12 (mask 12) (pidn 2300 12) L LI 29 pairWordA1 (Co2A.S 1) = true := by
  quickRfl

theorem bgetA : allN 7 (fun t => Nat.beq (#[29, 0, 3, 4, 5, 2, 1] : Array Nat)[t]!
    (pg 12 (mask 12) ch75342a.BP t)) = true := by
  quickRfl

theorem bgetB : allN 7 (fun t => Nat.beq (#[29, 2, 3, 0, 5, 4, 1] : Array Nat)[t]!
    (pg 12 (mask 12) ch75342b.BP t)) = true := by
  quickRfl

theorem orbA : (List.range 7).map (fun i => rcnt (ch75342a.LR i)) = [28, 256, 192, 2, 2, 1, 1] := by
  decide +kernel

theorem orbB : (List.range 7).map (fun i => rcnt (ch75342b.LR i)) =
    [120, 128, 32, 24, 1, 1, 1] := by
  decide +kernel

end CertificateChecks.KernelAsch54.Co2

end
