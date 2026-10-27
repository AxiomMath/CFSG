module

public import Certificates.Data.Kernel.WEMK

public section

namespace Certificates.B3MK

open Certificates.WEMK

@[expose] def mRow : Nat := 340282366920938463463374607431768211455

@[expose] def mCol : Nat :=
  169230327970901635135295839644110346096425308270070247419322710975022839007343212504332295614478952825321389459016200440774655

@[expose] def mL16 : Nat :=
  204583791292591926691396081575382549208529011407180575518006033900266475884974090617542369930984076593222635430161375266700549045759594884514604711935

@[expose] def mHi : Nat :=
  13407807883116368833931560660509329401596429402984471334422903279838487788309647712674135543865605663674450124786935712066531345228849969864127655754858480

@[expose] def m3 : Nat :=
  9365245653128492867539303345176587283521584408660131632776655248352779852825547750860259552803116346679910067757444507516619320016461198650245123

@[expose] def mB4 : Nat :=
  49947976816685295293542951174275132178781783512854035374808827991214825881736254671254717614949953848959520361373037373421969706754459726134640656

@[expose] def mE : Nat :=
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095

@[expose] def idW : Nat :=
  3121748550315992231381597229793166305748598142667107137895077869707766760525935172234908807585850085431411303632147046306061332512330903325769729

@[expose] def toW (A : NMat) : Nat :=
  ((List.range 4).flatMap fun i => (List.range 4).map fun j => ((A.getD i []).getD j 0) * 2 ^ (32 * (4 * i + j))).sum

@[expose] def red (P : Nat) : Nat := Nat.sub P (Nat.mul 13 (Nat.land (Nat.shiftRight (Nat.mul P 5042) 16) mL16))

@[expose] def lmul (g x : Nat) : Nat :=
  red (Nat.add
    (Nat.add (Nat.mul (Nat.land g mCol) (Nat.land x mRow))
      (Nat.mul (Nat.land (Nat.shiftRight g 32) mCol) (Nat.land (Nat.shiftRight x 128) mRow)))
    (Nat.add (Nat.mul (Nat.land (Nat.shiftRight g 64) mCol) (Nat.land (Nat.shiftRight x 256) mRow))
      (Nat.mul (Nat.land (Nat.shiftRight g 96) mCol) (Nat.shiftRight x 384))))

@[expose] def wfW (x : Nat) : Bool :=
  Nat.beq (Nat.shiftRight x 512) 0 && Nat.beq (Nat.land x mHi) 0 && Nat.beq (Nat.land (Nat.add x m3) mB4) 0

@[expose] def getE (Ep i : Nat) : Nat := Nat.land (Nat.shiftRight Ep (Nat.mul 512 i)) mE

@[expose] def get9 (Tp i : Nat) : Nat := Nat.land (Nat.shiftRight Tp (Nat.mul 9 i)) 511

@[expose] def o2q (q : Nat) : Bool := !(Nat.beq q idW) && Nat.beq (lmul q q) idW

@[expose] def o4q (q : Nat) : Bool := o2q (lmul q q)

@[expose] def o2W (a b : Nat) : Bool := o2q (lmul a b)

@[expose] def o4W (a b : Nat) : Bool := o4q (lmul a b)

@[expose] def memN (j : Nat) (J : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Nat.beq a j || ih) J

@[expose] def lenL {α : Type} (l : List α) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] def allWf (l : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun x _ ih => wfW x && ih) l

@[expose] def chainsOK (r0 r2 : Nat) (J VW : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih j => (!(o2W r0 x && o4W r2 x) || memN j J) && ih (Nat.succ j)) VW 0

@[expose] def stepOK (Ep n g x t : Nat) : Bool := Nat.blt t n && Nat.beq (lmul g x) (getE Ep t)

@[expose] def closeG (Ep Tp n x k : Nat) (gs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih c => stepOK Ep n g x (get9 Tp (Nat.add (Nat.mul 4 k) c)) && ih (Nat.succ c)) gs 0

@[expose] def elemsOK (Ep Tp n : Nat) (gs E : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => (wfW x && Nat.beq (getE Ep k) x && closeG Ep Tp n x k gs) && ih (Nat.succ k)) E 0

@[expose] def treeRow (Tp Dp n i0 k : Nat) (pc : Nat × Nat) : Bool :=
  (Nat.beq k i0 && Nat.beq (get9 Dp k) 0) ||
    (Nat.blt pc.1 n && Nat.blt pc.2 4 && Nat.beq (get9 Tp (Nat.add (Nat.mul 4 pc.1) pc.2)) k &&
      Nat.beq (get9 Dp k) (Nat.succ (get9 Dp pc.1)))

@[expose] def treeOK (Tp Dp n i0 : Nat) (par : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pc _ ih k => treeRow Tp Dp n i0 k pc && ih (Nat.succ k)) par 0

@[expose] def incrL (l : List Nat) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun x _ ih p => Nat.blt p x && ih x) l p

@[expose] def pick4 (a b c d l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) d c (Nat.beq l 2)) b (Nat.beq l 1)) a
    (Nat.beq l 0)

@[expose] def evalW (a b c d : Nat) (w : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X) (fun l _ ih X => ih (lmul (pick4 a b c d l) X)) w X

@[expose] def mwRow (Ep n r0 r2 r3 u x : Nat) (e : Nat × List Nat) : Bool :=
  (Nat.blt e.1 n && Nat.beq (getE Ep e.1) x) || Nat.beq (evalW r0 r2 r3 x e.2 idW) u

@[expose] def mwOK (Ep n r0 r2 r3 u : Nat) (VW : List Nat) (mw : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × List Nat) → Bool) (fun ms => List.rec (motive := fun _ => Bool) true
      (fun _ _ _ => false) ms)
    (fun x _ ih ms => List.rec (motive := fun _ => Bool) false (fun e rest _ => mwRow Ep n r0 r2 r3 u x e && ih rest) ms)
    VW mw

@[expose] def notIn (x : Nat) (H : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => !(Nat.beq h x) && ih) H

@[expose] def commZ (s z : Nat) : Bool := Nat.beq (lmul s z) (lmul z s)

@[expose] def witOK (sa sb z : Nat) (H : List Nat) : Bool := commZ sa z && commZ sb z && notIn sa H && notIn sb H

@[expose] def zOf (r0 r2 r3 : Nat) : Nat := (fun w => lmul w (lmul w w)) (lmul r0 (lmul r2 r3))

@[expose] def ck51 (r0 r2 r3 : Nat) (H : List Nat) (Hp Tp i0 sa sb : Nat) : Bool :=
  Nat.blt i0 (lenL H) && Nat.beq (getE Hp i0) idW && elemsOK Hp Tp (lenL H) [r0, r2, r3] H && !(Nat.beq sa sb) && witOK sa sb (zOf r0 r2 r3) H

end Certificates.B3MK

end
