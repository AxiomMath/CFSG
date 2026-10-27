module

public import Certificates.Data.Kernel.B433Alt.Chain
public import Certificates.Data.Kernel.B433Alt.Trace

public section

namespace CFSG.KC.B4A

@[expose] noncomputable def orbChunks (LP RD RW EL EW : Nat → Nat) (j l G nG : Nat) :
    List (Nat × Nat) → Nat → Nat
  | [], S => S
  | p :: cs, S => orbChunks LP RD RW EL EW j l G nG cs (orbRun LP RD RW EL EW j l G nG p.1 p.2 S)

@[expose] noncomputable def stabsAt (RD : Nat → Nat) (N G nG j : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => andB acc (stabAt RD N (fld G (Nat.mul (nat_lit 20) k) (ones (nat_lit 20))) j)) nG

@[expose] noncomputable def labOK (LP RD RW PW : Nat → Nat) (N j : Nat) (w : List Nat)
    (J a p G nG : Nat) (cs : List (Nat × Nat)) (o : Nat) : Bool :=
  andB (trOK LP RD RW PW N (nat_lit 0) (nat_lit 0) w J j a)
  (andB (wInH a) (andB (Nat.blt p (nat_lit 31671)) (andB (Nat.beq (ev1 LP a (nat_lit 0)) p)
  (andB (Nat.beq (orbCount (orbChunks LP RD RW (fun _ => 0) (fun _ => 0) j 0 G nG cs
      (orbInit p))) o)
    (stabsAt RD N G nG j)))))

end CFSG.KC.B4A

end
