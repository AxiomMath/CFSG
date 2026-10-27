module

public import Certificates.Data.SmithL6Aut
public import Certificates.Data.Kernel.Sym6Sq

public section

namespace CFSG.KC.SmithL6D

open CFSG.SmithL6 CFSG.KC.Sym6Sq

@[expose] noncomputable def hp : Nat := 102721

@[expose] noncomputable def mskK (c : Nat) : Nat := spanMask (c % 64) (c / 64 % 64) (c / 4096)

@[expose] noncomputable def annK (c : Nat) : Nat := annMaskOf (c % 64) (c / 64 % 64) (c / 4096)

@[expose] noncomputable def fF (x : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.mul (Nat.land x 1) 12297829382473034410)
    (Nat.mul (Nat.land (Nat.shiftRight x 1) 1) 14757395258967641292))
    (Nat.xor (Nat.mul (Nat.land (Nat.shiftRight x 2) 1) 17361641481138401520)
      (Nat.mul (Nat.land (Nat.shiftRight x 3) 1) 18374966859414961920)))
    (Nat.xor (Nat.mul (Nat.land (Nat.shiftRight x 4) 1) 18446462603027742720)
      (Nat.mul (Nat.land (Nat.shiftRight x 5) 1) 18446744069414584320))

@[expose] noncomputable def gU (U : Nat) : Nat :=
  Nat.xor 18446744073709551615 (Nat.land U 18446744073709551615)

@[expose] noncomputable def annK2 (c : Nat) : Nat :=
  gU (Nat.lor (Nat.lor (fF (Nat.mod c 64)) (fF (Nat.mod (Nat.div c 64) 64)))
    (fF (Nat.mod (Nat.div c 4096) 64)))

@[expose] noncomputable def fFB : Bool :=
  (List.range 64).all fun φ => (List.range 64).all fun x => form φ x == (fF x).testBit φ

@[expose] noncomputable def lane11 (T r : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.add 64 (Nat.mul 11 r))) 2047

@[expose] noncomputable def lane64 (P k : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul 64 k)) 18446744073709551615

@[expose] noncomputable def bldT (LM : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun m _ ih k acc =>
      strictA (Nat.add (Nat.lor acc (Nat.shiftLeft k (Nat.add 64 (Nat.mul 11 (Nat.mod m hp))))) 1)
        fun a => strictA (Nat.succ k) fun k' => ih k' a) LM 0 0

@[expose] noncomputable def bldP (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => strictA (Nat.lor x (Nat.shiftLeft ih 64)) fun p => p) L

@[expose] noncomputable def okK (T PM PA k m a : Nat) : Bool :=
  Nat.beq (lane11 T (Nat.mod m hp)) k && Nat.beq (lane64 PM k) m && Nat.beq (lane64 PA k) a &&
    strictA (lane11 T (Nat.mod a hp)) fun j =>
      Nat.blt j 1395 && Nat.beq (lane64 PM j) a && Nat.beq (lane64 PA j) m

@[expose] noncomputable def loopK (T PM PA : Nat) (LM : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
    (fun m _ ih LA k => List.rec (motive := fun _ => Bool) false
      (fun a LA' _ => okK T PM PA k m a && strictA (Nat.succ k) (ih LA')) LA) LM

@[expose] noncomputable def dualK (W : List Nat) : Bool :=
  forceA (W.map mskK) fun LM => forceA (W.map annK2) fun LA =>
    strictA (bldT LM) fun T => strictA (bldP LM) fun PM => strictA (bldP LA) fun PA =>
      loopK T PM PA LM LA 0

end CFSG.KC.SmithL6D
