module

public import Certificates.Data.Kernel.Co1BW
public import CFSG.Monster.GMS.Griess13.Data
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.KC.G13

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.Monster.GMS.Griess13.Co1Data

@[expose] noncomputable def strictT {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def m576 : Nat := Nat.shiftLeft (nat_lit 1) (nat_lit 576)

@[expose] noncomputable def pk (x y : Nat) : Nat :=
  Nat.add (Nat.mod x m576) (Nat.shiftLeft (Nat.mod y m576) (nat_lit 576))

@[expose] noncomputable def sP (a : Nat) : Nat := Nat.shiftRight a (nat_lit 576)

@[expose] noncomputable def oneP : Nat := pk oneK oneK

@[expose] noncomputable def mulP (a b : Nat) : Nat :=
  strictN a fun a => strictN b fun b => pk (mulWK a b) (mulWK (sP b) (sP a))

@[expose] noncomputable def invP (a : Nat) : Nat := strictN a fun a => pk (sP a) a

@[expose] noncomputable def powP (a : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneP (fun _ acc => mulP acc a) n

@[expose] noncomputable def zpowP (a : Nat) (e : Int) : Nat :=
  if 0 ≤ e then powP a e.toNat else powP (invP a) (-e).toNat

@[expose] noncomputable def conjP (a b : Nat) : Nat := strictN a fun a => mulP (mulP a b) (invP a)

@[expose] noncomputable def letterP (gens : List Nat) (l : Int) : Nat :=
  if 0 < l then gens.getD (l.toNat - 1) oneP else invP (gens.getD ((-l).toNat - 1) oneP)

@[expose] noncomputable def wordFrom (gens : List Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulP acc (letterP gens l)) ih) w

@[expose] noncomputable def wordP (gens : List Nat) (w : List Int) : Nat := wordFrom gens w oneP

@[expose] noncomputable def eqP (a b : Nat) : Bool := eqK a b

@[expose] noncomputable def iotaP (E : Fin 6 → Nat) (v : Fin 6 → Nat) : Nat :=
  (List.ofFn fun i => powP (E i) (v i)).foldr mulP oneP

@[expose] noncomputable def iotaC (E : Fin 6 → Nat) (c : Nat) : Nat :=
  iotaP E fun i => Nat.mod (Nat.div c (Nat.pow (nat_lit 3) i.val)) (nat_lit 3)

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n

@[expose] noncomputable def iotaNeK (E : Fin 6 → Nat) : Bool :=
  allN (nat_lit 27) fun h => allN (nat_lit 27) fun l =>
    (fun c => Bool.rec (motive := fun _ => Bool) (Bool.not (eqP (iotaC E c) oneP)) true
      (Nat.beq c (nat_lit 0))) (Nat.add (Nat.mul (nat_lit 27) h) l)

@[expose] noncomputable def lookupP : List (Nat × Nat) → Nat → Nat
  | [], _ => oneP
  | (k, v) :: l, i => if i = k then v else lookupP l i

@[expose] noncomputable def initP : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | x :: l, j => (j, x) :: initP l (j + 1)

@[expose] noncomputable def lineP (R : List (Nat × Nat)) (l : Nat × List (Nat × Int)) : Nat :=
  l.2.foldl (fun acc f => mulP acc (zpowP (lookupP R f.1) f.2)) oneP

@[expose] noncomputable def runP (ls : List (Nat × List (Nat × Int))) :
    List (Nat × Nat) → List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat)) (fun R => R)
    (fun l _ ih R => strictT (lineP R l) fun v => ih ((l.1, v) :: R)) ls

@[expose] noncomputable def evalP (p : SLP) (ins : List Nat) : List Nat :=
  p.outs.map fun f => zpowP (lookupP (runP p.lines (initP ins 1)) f.1) f.2

@[expose] noncomputable def digC (d : Nat) : Char := Char.ofNat (Nat.add (nat_lit 48) d)

@[expose] noncomputable def digK (f : Nat) : Nat → List Char → List Char :=
  Nat.rec (motive := fun _ => Nat → List Char → List Char) (fun _ ds => ds)
    (fun _ ih n ds => Bool.rec (motive := fun _ => List Char)
      (ih (Nat.div n (nat_lit 10)) (digC (Nat.mod n (nat_lit 10)) :: ds))
      (digC (Nat.mod n (nat_lit 10)) :: ds) (Nat.beq (Nat.div n (nat_lit 10)) (nat_lit 0))) f

@[expose] noncomputable def natC (n : Nat) : List Char := digK (Nat.succ n) n []

@[expose] noncomputable def intC (e : Int) : List Char :=
  Int.rec (motive := fun _ => List Char) natC (fun m => '-' :: natC (Nat.succ m)) e

@[expose] noncomputable def factC (f : Nat × Int) : List Char :=
  if f.2 = 1 then natC f.1 else ['^'].intercalate [natC f.1, intC f.2]

@[expose] noncomputable def lineC (l : Nat × List (Nat × Int)) : List Char :=
  ['='].intercalate [natC l.1, [' '].intercalate (l.2.map factC)]

@[expose] noncomputable def slpC (p : SLP) : List Char :=
  ['|'].intercalate [[';'].intercalate (p.lines.map lineC), [' '].intercalate (p.outs.map factC)]

@[expose] def unzig (z : Nat) : Int :=
  if z % 2 = 0 then ((z / 2 : Nat) : Int) else -(((z + 1) / 2 : Nat) : Int)

@[expose] def decFacts : List Nat → List (Nat × Int)
  | r :: z :: t => (r, unzig z) :: decFacts t
  | _ => []

@[expose] def decSLP (L : List (List Nat)) (O : List Nat) : SLP :=
  ⟨L.map fun l => (l.headD 0, decFacts l.tail), decFacts O⟩

@[expose] noncomputable def charsEq (a : List Char) : List Char → Bool :=
  List.rec (motive := fun _ => List Char → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y t _ => Bool.rec (motive := fun _ => Bool) false (ih t) (Nat.beq x.toNat y.toNat)) b) a

end CFSG.KC.G13

end
