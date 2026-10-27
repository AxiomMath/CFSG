module

public import Certificates.Data.Kernel.TabWordK
public import CFSG.CGT.M24R.R3Inputs
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.KC.M24R3

open CFSG.KC.Enum CFSG.KC.TabWord CFSG.CGT.M24R CFSG.CGT.M24R.R3 CFSG.Sporadic.Th.Native

@[expose] noncomputable def gP (z : Int) : Nat := pmk 24 5 fun i => ap (letTab z) i

@[expose] noncomputable def withL (L : Int → Nat) (k : (Int → Nat) → Bool) : Bool :=
  strictB (L 1) fun p1 => strictB (L 2) fun p2 => strictB (L 3) fun p3 =>
  strictB (L 4) fun p4 => strictB (L 5) fun p5 => strictB (L 6) fun p6 =>
  strictB (L 7) fun p7 => strictB (L 8) fun p8 => strictB (L 9) fun p9 =>
  strictB (L 10) fun p10 =>
  strictB (L (-1)) fun q1 => strictB (L (-2)) fun q2 => strictB (L (-3)) fun q3 =>
  strictB (L (-4)) fun q4 => strictB (L (-5)) fun q5 => strictB (L (-6)) fun q6 =>
  strictB (L (-7)) fun q7 => strictB (L (-8)) fun q8 => strictB (L (-9)) fun q9 =>
  strictB (L (-10)) fun q10 =>
  k fun z => if z = 1 then p1 else if z = 2 then p2 else if z = 3 then p3 else if z = 4 then p4
    else if z = 5 then p5 else if z = 6 then p6 else if z = 7 then p7 else if z = 8 then p8
    else if z = 9 then p9 else if z = 10 then p10 else if z = -1 then q1 else if z = -2 then q2
    else if z = -3 then q3 else if z = -4 then q4 else if z = -5 then q5 else if z = -6 then q6
    else if z = -7 then q7 else if z = -8 then q8 else if z = -9 then q9
    else if z = -10 then q10 else L z

@[expose] noncomputable def eqWd (L : Int → Nat) (w w' : N0Word) : Bool :=
  Nat.beq (wordK 24 5 (pidn 24 5) L (w.map letZ)) (wordK 24 5 (pidn 24 5) L (w'.map letZ))

@[expose] noncomputable def relK (L : Int → Nat) : Bool :=
  withL L fun L => relsN8Ten.all fun r => eqWd L r []

@[expose] noncomputable def idK (L : Int → Nat) : Bool :=
  withL L fun L =>
    eqWd L (thExp uD) (dExp uD) && eqWd L (nW ++ dExp uD ++ inv10 nW) (dExp bD) &&
      eqWd L (thExp bD) aW && !eqWd L aW [] &&
      (List.finRange 4).all (fun j =>
        eqWd L (inv10 nW ++ thExp (yD j) ++ nW) (dExp (a1D j)) &&
          eqWd L (nW ++ thExp (a1D j) ++ inv10 nW) (dExp (b1D j)) &&
          eqWd L (inv10 wW ++ dExp (yD j) ++ wW) (thExp (b1D j))) &&
      (List.finRange 16).all fun i => (List.finRange 4).all fun j =>
        eqWd L (eW i ++ dExp (yD j)) (dExp (yD j) ++ eW i)

@[expose] noncomputable def distK (L : Int → Nat) : Bool :=
  withL L fun L =>
    ((List.finRange 16).all fun i => (List.finRange 16).all fun i' =>
      i == i' || !eqWd L (eW i) (eW i')) &&
    (List.finRange 16).all fun v => (List.finRange 16).all fun v' =>
      v == v' || !eqWd L (tWordOf v) (tWordOf v')

end CFSG.KC.M24R3

end
