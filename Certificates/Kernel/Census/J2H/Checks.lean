module

public import Certificates.Kernel.Census.J2H.Chains
public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2H

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelJ2Cover CFSG.ComponentClassification.J2Cover

@[expose] def posW (w : List Nat) : List Int := w.map Int.ofNat

@[expose] def invW (w : List Int) : List Int := (w.map Neg.neg).reverse

@[expose] def expandW (subs : List (List Int)) (w : List Nat) : List Int :=
  w.flatMap fun l => subs.getD (l - 1) []

@[expose] def xW : List Int := [1, 2, 2, 2]

@[expose] def yW : List Int := [2, 2, 2, 2, 2, 2]

@[expose] def g1W : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2]

@[expose] def g2W : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2]

@[expose] def s0Ws : List (List Nat) :=
  [[2, 1, 2, 1, 2, 2], [1, 1, 2, 2, 2, 1, 2, 1], [1, 2, 2, 1, 1, 2, 2, 1]]

@[expose] def a5Ws : List (List Nat) := [[2, 1, 2, 2, 1, 2], [1, 1, 2, 2]]

@[expose] def a5Comm : List (List Int) :=
  [posW [2, 2] ++ posW [2, 1] ++ invW (posW [2, 2]) ++ invW (posW [2, 1]),
    posW [2, 1, 2] ++ posW [1, 1, 1] ++ invW (posW [2, 1, 2]) ++ invW (posW [1, 1, 1])]

@[expose] def vWs : List (List Nat) :=
  [[1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 1], [1, 1, 2, 2, 1, 1, 2, 2], [1, 2, 2, 1, 1, 2, 2, 1]]

@[expose] noncomputable def wA (wd : List Int) (r : Nat) : Bool :=
  wordEqK 315 9 (mask 9) (pidn 315 9) C2A.S C2A.SI 5 wd r

theorem x_pow : wA (xW ++ xW ++ xW ++ xW ++ xW) (pidn 315 9) = true := by quickRfl

theorem y_pow : wA (yW ++ yW ++ yW ++ yW ++ yW) (pidn 315 9) = true := by quickRfl

theorem x_val : wA xW (wordK 315 9 (mask 9) (pidn 315 9) C2A.S C2A.SI xW) = true := by quickRfl

theorem y_val : wA yW (wordK 315 9 (mask 9) (pidn 315 9) C2A.S C2A.SI yW) = true := by quickRfl

theorem x_ne : neK 315 9 (mask 9) (315 * 9) (wordK 315 9 (mask 9) (pidn 315 9) C2A.S C2A.SI xW)
    (pidn 315 9) = true := by quickRfl

theorem y_ne : neK 315 9 (mask 9) (315 * 9) (wordK 315 9 (mask 9) (pidn 315 9) C2A.S C2A.SI yW)
    (pidn 315 9) = true := by quickRfl

theorem g1_xy : wA (expandW [xW, yW] g1W) (C2A.S 0) = true := by quickRfl

theorem g2_xy : wA (expandW [xW, yW] g2W) (C2A.S 1) = true := by quickRfl

theorem s0_z : arrBind twoAArr 315 9 (S0C.S 0) = true := by quickRfl

theorem s0_words : ∀ i < 3, wA (posW (s0Ws.getD i [])) (S0C.S (i + 1)) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem v_words : ∀ i < 4, wA (posW (vWs.getD i [])) (VC.S i) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem a5_words : ∀ i < 2, wordEqK 315 9 (mask 9) (pidn 315 9) C2B.S C2B.SI 4
    (posW (a5Ws.getD i [])) (A5C.S i) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem a5_comm : ∀ i < 2, wordEqK 315 9 (mask 9) (pidn 315 9) A5C.S A5C.SI 2
    (a5Comm.getD i []) (A5C.S i) = true := by
  intro i hi
  interval_cases i <;> quickRfl

end CertificateChecks.KernelJ2H
