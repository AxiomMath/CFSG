module

public import Certificates.Kernel.Co2Cent.Data
public import Certificates.Kernel.Co2Cent.CentData
public import Certificates.Data.Kernel.OrbRow.Cent
public import Certificates.Kernel.Co2I301.ChainL
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp

@[expose] noncomputable def RGp (j : Nat) : Nat := CertificateChecks.KernelCo2I301.CH.F (Nat.add 33 j)

@[expose] noncomputable def tAct (j e : Nat) : Nat := pcomp 2300 12 4095 (getS TG j) e

@[expose] noncomputable def rAct (j key : Nat) : Nat := mapKey 12 4095 (RGp j) 5 key

@[expose] noncomputable def maskDecK (M : List Nat) (nl : Nat) : Bool :=
  allN (Nat.sub nl 1) (fun i => strictB (getS M (Nat.succ i)) fun a =>
    Nat.beq (Nat.land a (getS M i)) a)

theorem ch17351_x : bAnd(fixSetK 2300 12 4095 xA (BA.take 5),
    bAnd(powIdK 2300 12 4095 xA 3, bAnd(movesK 2300 12 4095 xA,
    lvCommK 2300 12 4095 SA 16 (getS MA 5) xA))) = true := by
  quickRfl

theorem ch17351_c : bAnd(wordEqK 2300 12 SA 16 65535 c1 (getLs W 0),
    bAnd(wordEqK 2300 12 SA 16 65535 c2 (getLs W 1),
    bAnd(wordEqK 2300 12 SA 16 65535 c5 (getLs W 2),
    bAnd(wordEqK 2300 12 SA 16 65535 g0 (getLs W 3),
    bAnd(commOK 2300 12 4095 c1 xA, bAnd(commOK 2300 12 4095 c2 xA,
    bAnd(commOK 2300 12 4095 c5 xA, bAnd(!(commOK 2300 12 4095 g0 xA),
    bAnd(actFK 12 4095 c1 BA [1, 2, 0, 3, 4], bAnd(actFK 12 4095 c2 BA [1, 2, 3, 4, 0],
    bAnd(actFK 12 4095 g0 BA [1, 0, 2, 3, 4],
    bAnd(powIdK 2300 12 4095 c5 5, bAnd(movesK 2300 12 4095 c5,
      !(allN 4 (fun j => commOK 2300 12 4095 c5 (RGp j)))))))))))))))) = true := by
  quickRfl

theorem ch17351_w : bAnd(allN 4 (fun j => wordEqK 2300 12 SA 16 (getS MA 5) (getS TG j) (getLs TW j)),
    bAnd(Nat.beq (lenS TG) 4,
      allN 4 (fun j => wordEqK 2300 12 SA 16 (getS MA 5) (RGp j) (getLs RW j)))) = true := by
  quickRfl

theorem ch17351_t : bAnd(orbRecK tAct (fun e => e) 4 8 255 (pidn 2300 12) 32 TE TR,
    ncAllK 2300 12 4095 (pidn 2300 12) RGp 4 TE) = true := by
  quickRfl

theorem ch17351_r :
    orbRecK rAct (revKey 12 4095 5) 4 16 65535 (subKey 12 BA 5 5) 243 RK RR = true := by
  quickRfl

theorem ch17351_n : bAnd(normK 2300 12 4095 RGp 4 c1 BA 5 5 RK,
    bAnd(normK 2300 12 4095 RGp 4 c2 BA 5 5 RK,
      allN 16 (fun j => bIf(Nat.beq fld(getS MA 5, j, 1) 1,
        normK 2300 12 4095 RGp 4 (getS SA j) BA 5 5 RK, true)))) = true := by
  quickRfl

theorem ch17351_m : bAnd(maskDecK MA 10, bAnd(maskDecK MB 7, maskDecK ML 3)) = true := by
  quickRfl

end CFSG.KD.Co2Cent

end
