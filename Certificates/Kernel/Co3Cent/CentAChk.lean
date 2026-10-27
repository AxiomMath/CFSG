module

public import Certificates.Kernel.Co3Cent.Trees
public import Certificates.Kernel.Co3Cent.CentAData
public import Certificates.Kernel.Co3Cent.Hex
public import Certificates.Data.Kernel.OrbRow.Cent
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow

@[expose] noncomputable def xAp : Nat := CertificateChecks.KernelCo3T.DE 9

@[expose] noncomputable def RGp (j : Nat) : Nat := CertificateChecks.KernelCo3Cent.CH.F (Nat.add 31 j)

@[expose] noncomputable def tActA (j e : Nat) : Nat := pcomp 276 9 511 (getS TG j) e

@[expose] noncomputable def rActA (j key : Nat) : Nat := mapKey 9 511 (RGp j) 5 key

@[expose] noncomputable def zMulAK (a b : Nat) : Bool :=
  bIf(Nat.beq a b, true, bIf(Nat.beq a (pcomp 276 9 511 xAp b), true,
    Nat.beq a (pcomp 276 9 511 xAp (pcomp 276 9 511 xAp b))))

@[expose] noncomputable def fixFA (g : Nat) : Bool :=
  allN 6 (fun t => strictB (getS BA t) fun b => Nat.beq (pg 9 511 g b) b)

@[expose] noncomputable def inCA (g : Nat) : Bool :=
  bAnd(inP3K (List.cons g List.nil) 0, commOK 276 9 511 g xAp)

@[expose] noncomputable def upw (u e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 276 9) (fun _ acc => pcomp 276 9 511 u acc) e

@[expose] noncomputable def badA (s : Nat) : Bool :=
  bIf(allN 5 (fun j => zMulAK (pcomp 276 9 511 s (RGp j)) (pcomp 276 9 511 (RGp j) s)), false, true)

theorem ch17370_xa : bAnd(fixSetK 276 9 511 xAp (BA.take 6),
    bAnd(powIdK 276 9 511 xAp 3, bAnd(movesK 276 9 511 xAp,
    bAnd(Nat.blt JK 17, bAnd(Nat.beq fld(getS MA 6, JK, 1) 1,
      !(commOK 276 9 511 (getS SA JK) xAp)))))) = true := by
  quickRfl

theorem ch17370_ra : bAnd(allN 5 (fun j => bAnd(inCA (RGp j), fixFA (RGp j))),
    allN 5 (fun i => allN 5 fun j =>
      zMulAK (pcomp 276 9 511 (RGp i) (RGp j)) (pcomp 276 9 511 (RGp j) (RGp i)))) = true := by
  quickRfl

theorem ch17370_rk : bAnd(orbRecK rActA (revKey 9 511 5) 5 16 65535 (subKey 9 BA 6 5) 243 RK RR,
    memK (mapKey 9 511 xAp 5 (subKey 9 BA 6 5)) RK) = true := by
  quickRfl

theorem ch17370_rn : bAnd(allN 17 (fun j => normK 276 9 511 RGp 5 (getS SHA j) BA 6 5 RK),
    allN 2 (fun j => normK 276 9 511 RGp 5 (getS U j) BA 6 5 RK)) = true := by
  quickRfl

theorem ch17370_ta : bAnd(orbRecK tActA (fun e => e) 3 8 255 (pidn 276 9) 32 TE TR,
    bAnd(allN 3 (fun j => inCA (getS TG j)), ncAllK 276 9 511 (pidn 276 9) RGp 5 TE)) = true := by
  quickRfl

theorem ch17370_c5 : bAnd(inCA C5, bAnd(powIdK 276 9 511 C5 5, bAnd(movesK 276 9 511 C5,
    !(allN 5 (fun j => commOK 276 9 511 C5 (RGp j)))))) = true := by
  quickRfl

theorem ch17370_u : strictB (getS U 0) (fun u1 => strictB (getS U 1) fun u2 =>
    bAnd(inCA u1, bAnd(inCA u2,
    bAnd(Nat.beq (getS U3 0) (upw u1 3), bAnd(Nat.beq (getS U3 1) (upw u2 3),
    bAnd(Nat.beq (pcomp 276 9 511 u1 u2) (pcomp 276 9 511 (getS U3 2) (pcomp 276 9 511 u2 u1)),
    bAnd(allN 3 (fun t => bAnd(fixFA (getS U3 t),
      memK (mapKey 9 511 (getS U3 t) 5 (subKey 9 BA 6 5)) RK)),
    bAnd(allN 8 (fun t => Nat.beq (getS SAB t)
      (pcomp 276 9 511 (upw u1 (Nat.mod (Nat.succ t) 3)) (upw u2 (Nat.div (Nat.succ t) 3)))),
      allN 8 (fun t => badA (getS SAB t)))))))))) = true := by
  quickRfl

end CFSG.KD.Co3Cent

end
