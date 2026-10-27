module

public import Certificates.Data.Kernel.F4Mat

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def bitN (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) (nat_lit 1)

@[expose] noncomputable def frow (M i : Nat) : Nat := fget M i (nat_lit 6)

@[expose] noncomputable def mat (L k : Nat) : Nat := fget L k (nat_lit 36)

@[expose] noncomputable def ID6 : Nat := nat_lit 34630287489

@[expose] noncomputable def par6 (x : Nat) : Nat := Nat.land (popc (nat_lit 6) x) (nat_lit 1)

@[expose] noncomputable def bmulK (A B : Nat) : Nat :=
  strictN A fun A => nIf(Nat.beq A (nat_lit 0), nat_lit 0, strictN B fun B =>
    nIf(Nat.beq B (nat_lit 0), nat_lit 0,
      orN (nat_lit 6) fun i => Nat.shiftLeft
        (xorN (nat_lit 6) fun l => nIf(Nat.beq (bitN (frow A i) l) (nat_lit 1), frow B l, nat_lit 0))
        (Nat.mul (nat_lit 6) i)))

@[expose] noncomputable def bvecK (A v : Nat) : Nat :=
  orN (nat_lit 6) fun i => Nat.shiftLeft (par6 (Nat.land (frow A i) v)) i

@[expose] noncomputable def btraceK (M : Nat) : Nat :=
  xorN (nat_lit 6) fun i => bitN (frow M i) i

@[expose] noncomputable def antiK (Z A : Nat) : Nat := Nat.xor (bmulK Z A) (bmulK A Z)

@[expose] noncomputable def ent4 (A i j : Nat) : Nat := ent A i j

@[expose] noncomputable def mul4K (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    mk fun i j => sumN (nat_lit 6) fun k => Nat.mul (ent4 A i k) (ent4 B k j)

@[expose] noncomputable def add4K (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B => mk fun i j => Nat.add (ent4 A i j) (ent4 B i j)

@[expose] noncomputable def sub4K (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    mk fun i j => Nat.add (ent4 A i j) (Nat.mul (nat_lit 3) (ent4 B i j))

@[expose] noncomputable def lift2K (M : Nat) : Nat :=
  strictN M fun M => mk fun i j => bitN (frow M i) j

@[expose] noncomputable def qK (e : Nat) (x : Nat) : Nat := bitN e x

@[expose] noncomputable def bfK (e : Nat) (x y : Nat) : Nat :=
  Nat.xor (Nat.xor (qK e (Nat.xor x y)) (qK e x)) (qK e y)

@[expose] noncomputable def reflBK (e : Nat) (v x : Nat) : Nat :=
  Nat.xor x (nIf(Nat.beq (bfK e x v) (nat_lit 1), v, nat_lit 0))

@[expose] noncomputable def reflRowsK (e : Nat) (v : Nat) : Nat :=
  orN (nat_lit 6) fun i => Nat.shiftLeft
    (orN (nat_lit 6) fun j => Nat.shiftLeft (bitN (reflBK e v (pw2 j)) i) j) (Nat.mul (nat_lit 6) i)

@[expose] noncomputable def wordRowsK (G : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ID6 (fun s _ ih => bmulK (mat G s) ih) w

@[expose] noncomputable def ptilK (G C s : Nat) : Nat :=
  add4K (lift2K (mat G s)) (add4K (lift2K (mat C s)) (lift2K (mat C s)))

@[expose] noncomputable def prod4K (G C : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun s _ ih => mul4K (ptilK G C s) ih) w

end CFSG.KC.O8

end
