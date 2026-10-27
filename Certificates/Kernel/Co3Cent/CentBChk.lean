module

public import Certificates.Kernel.Co3Cent.Trees
public import Certificates.Kernel.Co3Cent.CentBData
public import Certificates.Data.Kernel.OrbRow.Cent
public import Certificates.Data.Kernel.OrbRow.CentB
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow

@[expose] noncomputable def xBp : Nat := CertificateChecks.KernelCo3T.DE 1

@[expose] noncomputable def DGp (j : Nat) : Nat := CertificateChecks.KernelCo3T.DE (Nat.pow 3 j)

@[expose] def KPB : List Nat := [0, 21, 43, 47, 88, 105, 1]

@[expose] noncomputable def tActB (j e : Nat) : Nat := pcomp 276 9 511 (getS TGB j) e

@[expose] noncomputable def e5Act (j e : Nat) : Nat := pcomp 276 9 511 (getS SB (getS J5 j)) e

@[expose] noncomputable def dActB (j key : Nat) : Nat := mapKey 9 511 (DGp j) 7 key

@[expose] noncomputable def inCB (g : Nat) : Bool :=
  bAnd(inP3K (List.cons g List.nil) 0, commOK 276 9 511 g xBp)

@[expose] noncomputable def maskOf (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun j _ acc => Nat.lor (Nat.shiftLeft 1 j) acc) L

theorem ch17370_xb : bAnd(fixSetK 276 9 511 xBp (BB.take 15),
    bAnd(powIdK 276 9 511 xBp 3, movesK 276 9 511 xBp)) = true := by
  quickRfl

theorem ch17370_cap :
    allN 6 (fun i => capK (getS DB i) (BB.take 15) (getS [15, 14, 9, 6, 2, 1] i)) = true := by
  quickRfl

theorem ch17370_deg : bAnd(allN 14 (fun t => degK 276 9 511 SB 14 (getS MB 1) (getS BB 1)
      (getS DB 2) (BB.take 15) (getS BB (Nat.succ t)) (getS DG t) (getLs UQ t)),
    bAnd(Nat.beq (lenS DG) 14, bAnd(Nat.beq (getS DG 0) 9,
      Nat.beq (cntK DG (fun d => Nat.beq d 9)) 12))) = true := by
  quickRfl

theorem ch17370_l4 : bAnd(wordEqK 276 9 SB 14 (getS MB 4) U4 WU4,
    bAnd(Nat.beq (pg 9 511 U4 (getS BB 4)) 162,
    bAnd(Nat.beq (maskOf J5) (getS MB 5), bAnd(Nat.beq (lenS J5) 3,
    bAnd(allN 3 (fun t => Nat.blt (getS J5 t) 14),
    bAnd(orbRecK e5Act (fun e => e) 3 8 255 (pidn 276 9) 12 E5 E5R,
    bAnd(Nat.beq (lenS UE) 12,
    bAnd(allN 12 (fun t => Nat.beq (getS UE t) (pcomp 276 9 511 U4 (getS E5 t))),
      ncAllK 276 9 511 (pidn 276 9) (fun _ => xBp) 1 UE)))))))) = true := by
  quickRfl

theorem ch17370_d : bAnd(allN 5 (fun j => inCB (DGp j)),
    bAnd(allN 6 (fun t => Nat.beq (getS KPB t) (getS BB t)),
    bAnd(Nat.beq (getS KPB 6) (getS BB 15),
      orbRecK dActB (revKey 9 511 7) 5 16 65535 (subKey 9 KPB 0 7) 243 DK DR))) = true := by
  quickRfl

theorem ch17370_dn : bAnd(allN 12 (fun j => normK 276 9 511 DGp 5 (getS SHB j) KPB 0 7 DK),
    normK 276 9 511 DGp 5 C3 KPB 0 7 DK) = true := by
  quickRfl

theorem ch17370_tb : bAnd(orbRecK tActB (fun e => e) 2 8 255 (pidn 276 9) 8 TEB TRB,
    bAnd(allN 2 (fun j => inCB (getS TGB j)), ncAllK 276 9 511 (pidn 276 9) DGp 5 TEB)) = true := by
  quickRfl

theorem ch17370_c5b : bAnd(inCB C5B, bAnd(powIdK 276 9 511 C5B 5, bAnd(movesK 276 9 511 C5B,
    !(allN 5 (fun j => commOK 276 9 511 C5B (DGp j)))))) = true := by
  quickRfl

theorem ch17370_c3 : bAnd(inCB C3, bAnd(powIdK 276 9 511 C3 3,
    !(allN 5 (fun j => commOK 276 9 511 C3 (DGp j))))) = true := by
  quickRfl

end CFSG.KD.Co3Cent

end
