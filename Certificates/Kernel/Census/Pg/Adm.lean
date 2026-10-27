module

public import Certificates.Kernel.Census.Pg.ClsData
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kmisc_packarrs CertificateChecks.KernelPgAdm.AK CFSG.EvenSporadicStandard.Fin76b.W16.admArr 8

#kmisc_packarrs CertificateChecks.KernelPgAdm.AI CFSG.EvenSporadicStandard.Fin76b.W16.admIso 7

#kmisc_packarrs CertificateChecks.KernelPgAdm.ER CFSG.EvenSporadicStandard.Fin76b.W16.eTab 5

public section

namespace CertificateChecks.KernelPgAdm

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS
  CFSG.KC.Misc.ArrEnum CertificateChecks.KernelPgCls

theorem bind_ok : bAnd(allN 60 (fun m => arrBind admArr[m]! 128 8 (AK m)),
    bAnd(allN 60 (fun m => arrBind admIso[m]! 32 7 (AI m)),
    allN 32 (fun a => arrBind eTab[a]! 32 5 (ER a)))) = true := by
  decide +kernel

@[expose] noncomputable def pt (p c : Nat) : Nat := pg 8 (mask 8) p c

@[expose] noncomputable def MI : Nat := 4290772992

theorem mi_ok : allN 32 (fun c => Nat.blt 0 (Nat.land MI (Nat.shiftLeft 1 c)) ==
      bIf(Nat.beq c 0, false, bIf(Nat.beq c 21, false, Nat.beq (mulC c c) 0))) = true := by
  decide +kernel

@[expose] noncomputable def admK (p : Nat) : Bool :=
  bAnd(Nat.beq (pt p 32) 32, bAnd(Nat.beq (pt p 64) 85,
    bAnd(allN 32 (fun c => Nat.blt (pt p c) 32), bAnd(Nat.beq (fixK 32 8 p) 8,
    CFSG.KC.LQT.P.anyN 32 (fun c =>
      bAnd(Nat.blt 0 (Nat.land MI (Nat.shiftLeft 1 c)), Nat.beq (pt p c) c))))))

@[expose] noncomputable def scanK (lo cnt : Nat) : Bool :=
  allN cnt fun t => bIf(admK (TT (Nat.add lo t)), memK 60 AK (TT (Nat.add lo t)), true)

theorem scan_ok : scanK 0 10575 = true := by quickRfl

@[expose] noncomputable def IX (m : Nat) : Nat :=
  [10454, 10396, 10267, 10317, 10309, 10362, 10364, 10534, 10310, 10169, 10481, 10258, 10350, 10304,
    10446, 10498, 10521, 10530, 10296, 10348, 10306, 10487, 10518, 10550, 10504, 10548, 10451, 10269,
    10559, 10321, 10268, 10319, 10556, 10172, 10408, 10256, 10199, 10405, 10359, 10366, 10543, 10311,
    10179, 10416, 10460, 10294, 10146, 10459, 10181, 10357, 10407, 10148, 10509, 10345, 10167, 10439,
    10413, 10302, 10369, 10188].getD m 0

theorem adm_ok : allN 60 (fun m => bAnd(admK (AK m), bAnd(Nat.blt (IX m) 10575,
    bAnd(Nat.beq (TT (IX m)) (AK m),
    allN m (fun j => bIf(Nat.beq (AK m) (AK j), false, true)))))) = true := by
  quickRfl

theorem ix_ok : allN 60 (fun m => Nat.blt 10142 (IX m)) = true := by quickRfl

theorem perm_ok : allN 60 (fun m =>
    CFSG.KC.Enum.permOK 128 8 (mask 8) (128 * 8) (AK m) (pinvS 128 8 (mask 8) (AK m))) = true := by
  quickRfl

@[expose] noncomputable def eK (a b : Nat) : Nat := pg 5 (mask 5) (ER a) b

@[expose] noncomputable def ixPK (i k : Nat) : Nat :=
  if i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 then 32 * posD i + k else 32 * posD (dMul i 2) + eK k eT

@[expose] noncomputable def mulCK (a b : Nat) : Nat :=
  ixPK (dMul (decD a) (decD b)) (eK (a % 32) (b % 32))

@[expose] noncomputable def isoK (m : Nat) : Bool :=
  (fun p f => bAnd(Nat.beq (pg 7 (mask 7) f 0) 0, bAnd(Nat.beq (pg 7 (mask 7) f 21) 21,
    bAnd(allN 32 (fun k => bAnd(Nat.blt (pg 7 (mask 7) f k) 128,
      Nat.beq (pt p (pg 7 (mask 7) f k)) (pg 7 (mask 7) f k))),
    bAnd(allN 32 (fun a => allN 32 (fun b => Nat.beq (pg 7 (mask 7) f (eK a b))
      (mulCK (pg 7 (mask 7) f a) (pg 7 (mask 7) f b)))),
    bAnd(allN 32 (fun a => allN a (fun b =>
      bIf(Nat.beq (pg 7 (mask 7) f a) (pg 7 (mask 7) f b), false, true))),
    bAnd(allN 128 (fun c => bIf(Nat.beq (pt p c) c,
      CFSG.KC.LQT.P.anyN 32 (fun k => Nat.beq (pg 7 (mask 7) f k) c), true)),
    Nat.beq (foldN 128 (fun c s => Nat.add s (nIf(allN 128 (fun g =>
      bIf(Nat.beq (pt p g) g, Nat.beq (mulCK c g) (mulCK g c), true)), 1, 0))) 0) 8))))))) (AK m) (AI m)

theorem iso_ok0 : allN 15 (fun m => isoK m) = true := by quickRfl

theorem iso_ok1 : allN 15 (fun m => isoK (Nat.add 15 m)) = true := by quickRfl

theorem iso_ok2 : allN 15 (fun m => isoK (Nat.add 30 m)) = true := by quickRfl

theorem iso_ok3 : allN 15 (fun m => isoK (Nat.add 45 m)) = true := by quickRfl

theorem admK_neg : bIf(admK (TT 0), false, true) = true := by quickRfl

theorem iso_neg : bIf((fun f => allN 32 (fun a => allN 32 (fun b => Nat.beq (pg 7 (mask 7) f (eK b a))
    (mulCK (pg 7 (mask 7) f a) (pg 7 (mask 7) f b))))) (AI 0), false, true) = true := by
  quickRfl

theorem scan_neg : bIf(Nat.beq (TT (IX 0)) (AK 1), false, true) = true := by quickRfl

end CertificateChecks.KernelPgAdm

end
