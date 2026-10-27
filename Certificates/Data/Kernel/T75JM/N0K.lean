module

public import Certificates.Data.Kernel.TabWordK
public import Certificates.Data.Kernel.Misc.Base
public import CFSG.CGT.T75JM.N6A6
public import CFSG.CGT.T75JM.N6Rels
public import CFSG.CGT.T75JM.Interfaces
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM

@[expose] noncomputable def idn : Nat := pidn 22 5

@[expose] noncomputable def withL (L : Int → Nat) (k : (Int → Nat) → Bool) : Bool :=
  strictB (L 1) fun p1 => strictB (L 2) fun p2 => strictB (L 3) fun p3 =>
  strictB (L 4) fun p4 => strictB (L 5) fun p5 => strictB (L 6) fun p6 =>
  strictB (L (-1)) fun q1 => strictB (L (-2)) fun q2 => strictB (L (-3)) fun q3 =>
  strictB (L (-4)) fun q4 => strictB (L (-5)) fun q5 => strictB (L (-6)) fun q6 =>
  k fun z => if z = 1 then p1 else if z = 2 then p2 else if z = 3 then p3 else if z = 4 then p4
    else if z = 5 then p5 else if z = 6 then p6 else if z = -1 then q1 else if z = -2 then q2
    else if z = -3 then q3 else if z = -4 then q4 else if z = -5 then q5 else if z = -6 then q6
    else L z

@[expose] def a6W (a : Nat) : List (Fin 6 × Bool) :=
  (a6Words.getD a []).map fun i => (if i = 0 then 0 else 1, true)

@[expose] def lw (w : List (Fin 6 × Bool)) : List Int := (liftWord w).map m22LetterZ

@[expose] def a6Z (i : Nat) : Int := if i = 0 then 1 else 2

@[expose] def twZ (k : Nat) : List Int :=
  ((List.range 4).filter fun i => k.testBit i).map fun i => (i : Int) + 3

@[expose] noncomputable def ak (L : Int → Nat) (a : Nat) : Nat :=
  wordK 22 5 idn L ((a6Words.getD a []).map a6Z)

@[expose] noncomputable def tk (L : Int → Nat) (k : Nat) : Nat := wordK 22 5 idn L (twZ k)

@[expose] def hexad : List Nat := [0, 1, 2, 9, 17, 19]

@[expose] noncomputable def keyP (pts : List Nat) (g : Nat → Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.add (g p) (Nat.mul (nat_lit 32) ih)) pts

@[expose] noncomputable def keyL (pts : List Nat) (P : Nat) : Nat := keyP pts (fdN 5 P)

@[expose] noncomputable def ptW (L : Int → Nat) (u : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun z _ ih => strictN ih fun y => fdN 5 (L z) y) u

@[expose] noncomputable def fixOk (L : Int → Nat) : Bool :=
  (List.range 16).all fun k => strictB (tk L k) fun T => hexad.all fun p => Nat.beq (fdN 5 T p) p

@[expose] noncomputable def a6KeyOk (L : Int → Nat) : Bool :=
  nodupN (a6Words.map fun u => keyP hexad (ptW L (u.map a6Z)))

@[expose] noncomputable def allW (ws : List (List Nat)) (g : Nat → List Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun u _ ih i => g i u && ih (Nat.succ i)) ws

@[expose] noncomputable def tKeyOk (L : Int → Nat) : Bool :=
  nodupN ((List.range 16).map fun k => keyL (List.range 22) (tk L k))

@[expose] noncomputable def relOk (L : Int → Nat) : Bool :=
  rels6.all fun r => Nat.beq (wordK 22 5 idn L (lw r)) idn

@[expose] noncomputable def n0kOk (L : Int → Nat) : Bool :=
  withL L fun L => relOk L && fixOk L && a6KeyOk L && tKeyOk L

end CFSG.KC.N0K

end
