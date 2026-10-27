module

public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.Co2SmithR

open CFSG.KC.Enum CFSG.KC.N3153

@[expose] noncomputable def cgA (C v : Nat) : Nat := fld(C, Nat.mul (nat_lit 32) v, nat_lit 4294967295)

@[expose] noncomputable def fixA (Ts : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun T _ ih =>
    Nat.add (nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1, nat_lit 0))
      (Nat.mul (nat_lit 2) ih)) Ts

@[expose] noncomputable def initValA (Ts pre : List Nat) (v : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.pow (nat_lit 2) Ts.length) (idxK pre v)) (fixA Ts v)

@[expose] noncomputable def initA (n : Nat) (Ts pre : List Nat) : Nat :=
  foldN n (fun v a => Nat.add a (Nat.shiftLeft (initValA Ts pre v) (Nat.mul (nat_lit 32) v)))
    (nat_lit 0)

@[expose] noncomputable def accA (n : Nat) (S : Nat → Nat) (C : Nat) : Nat :=
  foldN n (fun w a => Nat.add a (Nat.mul (hcK (cgA C w)) (S w))) (nat_lit 0)

@[expose] noncomputable def newColA (Ts : List Nat) (C A v : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (List.foldl (fun a T => Nat.mod (Nat.add (Nat.mul a (nat_lit 1000003))
      (Nat.mod (cgA C (pg (nat_lit 12) (nat_lit 4095) T v)) (nat_lit 2147483629)))
      (nat_lit 2147483629)) (Nat.mod (cgA C v) (nat_lit 2147483629)) Ts) (nat_lit 1000003))
    fld(A, Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) v), nat_lit 281474976710655))
    (nat_lit 2147483629)

@[expose] noncomputable def stepA (n : Nat) (S : Nat → Nat) (Ts : List Nat) (C : Nat) : Nat :=
  strictN (accA n S C) fun A => foldN n (fun v a => Nat.add a (Nat.shiftLeft (newColA Ts C A v)
    (Nat.mul (nat_lit 32) v))) (nat_lit 0)

@[expose] noncomputable def colourA (n : Nat) (S : Nat → Nat) (Ts pre : List Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (initA n Ts pre) (fun _ C => strictN C fun C => stepA n S Ts C) k

@[expose] noncomputable def memA (l : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a v, true, ih)) l

@[expose] noncomputable def classA (n : Nat) (S : Nat → Nat) (Ts pre : List Nat) (k x : Nat)
    (pts : List Nat) : Bool :=
  strictB (colourA n S Ts pre k) fun C =>
    allN n fun w => bIf(Nat.beq (cgA C w) (cgA C x), memA pts w, true)

@[expose] noncomputable def singA (n : Nat) (S : Nat → Nat) (Ts pre : List Nat) (k lo m : Nat) :
    Bool :=
  strictB (colourA n S Ts pre k) fun C =>
    allN m fun i => strictB (cgA C (Nat.add lo i)) fun c =>
      allN n fun w => bIf(Nat.beq (cgA C w) c, Nat.beq w (Nat.add lo i), true)

end CFSG.KC.Co2SmithR

end
