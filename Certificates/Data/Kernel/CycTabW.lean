module

public import Certificates.Data.Kernel.CycTab

public section

namespace CFSG.KC.CycTabW

open CFSG.KC.CycTab

@[expose] noncomputable def fgW (w T f : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul f w)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def tabOKW (n w TT i : Nat) (F : Nat → Nat) : Bool :=
  allLtK n fun x =>
    Bool.rec false
      (Bool.rec false
        (Nat.beq (fgW w TT (Nat.add (Nat.mul (Nat.mul (nat_lit 2) i) n)
          (fgW w TT (Nat.add (Nat.mul (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)) n) x)))) x)
        (Nat.blt (fgW w TT (Nat.add (Nat.mul (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)) n) x))
          n))
      (Nat.beq (fgW w TT (Nat.add (Nat.mul (Nat.mul (nat_lit 2) i) n) x)) (F x))

@[expose] noncomputable def tabsOKW (n w TT : Nat) (F : Nat → Nat → Nat) (k : Nat) : Bool :=
  allLtK k fun i => tabOKW n w TT i (F i)

@[expose] noncomputable def wordW (n w TT : Nat) (ws : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun k _ ih => fgW w TT (Nat.add (Nat.mul k n) ih)) ws

@[expose] noncomputable def eqOKW (n w TT : Nat) (ws : List Nat) (F : Nat → Nat) : Bool :=
  allLtK n fun x => Nat.beq (wordW n w TT ws x) (F x)

@[expose] noncomputable def onesOKW (n w TT : Nat) (RS : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ws _ ih => Bool.rec false ih (eqOKW n w TT ws fun x => x)) RS

@[expose] def codeW {k : Nat} (l : Fin k × Bool) : Nat := 2 * l.1.val + cond l.2 0 1

end CFSG.KC.CycTabW

end
