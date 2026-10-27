module

public import Certificates.Data.Kernel.GammaUFrameK

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C

@[expose] noncomputable def anyB (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k ih => f k || ih) n

open CFSG.GF2Type.Smith1979.GammaU in
@[expose] noncomputable def cpCond (e : Nat) : Bool :=
  !(Nat.beq e 0) && !(q0b e) && !(Nat.beq e 3072) && !(Nat.beq e (theta0N 3072)) &&
    !(Nat.beq e (Nat.xor 3072 (theta0N 3072)))

@[expose] noncomputable def inCP (TE NE e : Nat) : Bool :=
  anyB NE fun n => Nat.beq (ap12 (look TE n) 3072) e

@[expose] noncomputable def killOK (S F e : Nat) : Bool :=
  allBelow 12 (fun j => Nat.beq (ap12 F (Nat.xor (ap12 S (2 ^ j)) (2 ^ j))) 0) &&
    !(Nat.beq (ap12 F e) 0)

@[expose] noncomputable def cpEnt (S TE NE e : Nat) (r : List Nat) : Bool :=
  bif Nat.beq (nthD 0 r 0) 0 then !(cpCond e) && !(inCP TE NE e)
  else bif Nat.beq (nthD 0 r 0) 1 then
    cpCond e && inCP TE NE e && Nat.blt (nthD 0 r 1) 4096 &&
      Nat.beq (Nat.xor (ap12 S (nthD 0 r 1)) (nthD 0 r 1)) e
  else cpCond e && !(inCP TE NE e) && killOK S (nthD 0 r 1) e

@[expose] noncomputable def cpOK (SL : List Nat) (S TE NE : Nat) (R : List (List Nat)) : Bool :=
  Nat.beq (lenN SL) (lenN R) && (List.zip SL R).all (fun p => cpEnt S TE NE p.1 p.2) &&
    allBelow NE fun n => memN (ap12 (look TE n) 3072) SL

end CFSG.KC.GUV

end
