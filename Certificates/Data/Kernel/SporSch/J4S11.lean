module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.Spor.PCount
public import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs

public section

namespace CFSG.KS.SporSch.J4E

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.PCnt

@[expose] def splitK (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | x :: xs => if x = c then [] :: splitK c xs else
      match splitK c xs with
      | [] => [[x]]
      | l :: ls => (x :: l) :: ls

@[expose] def digitsK : List Char → Nat → Option Nat
  | [], acc => some acc
  | x :: xs, acc => if x.isDigit then digitsK xs (10 * acc + (x.toNat - 48)) else none

@[expose] def natK : List Char → Option Nat
  | [] => none
  | l => digitsK l 0

@[expose] def lineK : List (List Char) → Option (Option (List Nat))
  | [] => some none
  | [['m', 'u'], i, j, k] => do return some [0, ← natK i, ← natK j, ← natK k]
  | [['i', 'v'], i, k] => do return some [1, ← natK i, ← natK k]
  | [['p', 'w', 'r'], e, i, k] => do return some [2, ← natK e, ← natK i, ← natK k]
  | t :: _ => if t.head? = some '#' then some none else none

@[expose] def parseK (cs : List Char) : Option (List (List Nat)) :=
  ((splitK '\n' cs).mapM fun l => lineK ((splitK ' ' l).filter fun t => !t.isEmpty)).map
    (List.filterMap id)

@[expose] def decodeK : List Nat → CFSG.Sporadic.GLQ.Instr
  | [0, i, j, k] => .mu i j k
  | [1, i, k] => .iv i k
  | [2, e, i, k] => .pwr e i k
  | _ => .mu 0 0 0

@[expose] noncomputable def powBJ (c rm one : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => one)
    (fun _ ih M e => nIf(Nat.beq e (nat_lit 0), one, nIf(Nat.beq e (nat_lit 1), M,
      strictN (ih (mulJ c rm M M) (Nat.div e (nat_lit 2))) fun Y =>
        nIf(Nat.beq (Nat.mod e (nat_lit 2)) (nat_lit 1), mulJ c rm M Y, Y)))) fuel

@[expose] noncomputable def expK (c rm one X Y Z : Nat) : Bool :=
  allN (nat_lit 1331) fun t =>
    Nat.beq (powJ c rm one (mulJ c rm (mulJ c rm (powJ c rm one X (Nat.mod t (nat_lit 11)))
      (powJ c rm one Y (Nat.mod (Nat.div t (nat_lit 11)) (nat_lit 11))))
      (powJ c rm one Z (Nat.mod (Nat.div t (nat_lit 121)) (nat_lit 11)))) (nat_lit 11)) one

@[expose] noncomputable def centerK (c rm one X Y : Nat) : Bool :=
  allN (nat_lit 120) fun t =>
    CFSG.KC.J4Q.strictB (mulJ c rm (powJ c rm one X (Nat.mod (Nat.succ t) (nat_lit 11)))
      (powJ c rm one Y (Nat.mod (Nat.div (Nat.succ t) (nat_lit 11)) (nat_lit 11)))) fun A =>
    notB (andB (Nat.beq (mulJ c rm A X) (mulJ c rm X A)) (Nat.beq (mulJ c rm A Y) (mulJ c rm Y A)))

@[expose] noncomputable def vecPowK (rm M : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun v => v) (fun _ ih v => ih (vecJ rm v M))

@[expose] noncomputable def appK (rm b : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun X _ ih n v => ih (Nat.div n b) (vecPowK rm X (Nat.mod n b) v))

@[expose] noncomputable def vecsK (rm b : Nat) (xs : List Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun n ih => appK rm b xs n (nat_lit 1) :: ih)

@[expose] noncomputable def distK (rm b : Nat) (xs : List Nat) (N : Nat) : Bool :=
  distB (vecsK rm b xs N)

@[expose] noncomputable def dK (one k : Nat) : Nat :=
  Nat.shiftLeft (Nat.shiftRight one (Nat.mul (nat_lit 128) k)) (Nat.mul (nat_lit 128) k)

@[expose] noncomputable def fixK (c rm one G P Pi R k : Nat) : Bool :=
  CFSG.KC.J4Q.strictB (mulJ c rm P (Nat.xor G one)) fun T =>
    andB (Nat.beq (mulJ c rm P Pi) one) (andB (Nat.beq (mulJ c rm Pi P) one)
      (andB (allN k fun i => Nat.beq (rowJ rm T i) (nat_lit 0)) (Nat.beq (mulJ c rm T R) (dK one k))))

end CFSG.KS.SporSch.J4E

end
