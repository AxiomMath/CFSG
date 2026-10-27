module

public import Certificates.Data.Kernel.SporSch.J4SSylow
public import Certificates.Data.Kernel.F4M3B
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def kfunK (E SQ : Nat → Nat) (n e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ _ => nat_lit 5)
    (fun _ ih n e m => nIf(bAnd(Nat.beq n (nat_lit 0), Nat.beq e (nat_lit 0)), m,
      strictN (Nat.xor n (appK (E e) n)) (fun n' => ih n' (SQ e) (Nat.succ m))))
    (nat_lit 5) n e (nat_lit 0)

@[expose] noncomputable def cntE (E SQ CT : Nat → Nat) (e : Nat) : Nat :=
  strictN (CT e) (fun c => foldN (nat_lit 2048) (fun n s => Nat.add s (Nat.shiftLeft (nat_lit 1)
    (Nat.mul (nat_lit 24) (Nat.add (Nat.mul (nat_lit 6) (Nat.add (ellK n) (Nat.mul (nat_lit 2) c)))
      (kfunK E SQ n e))))) (nat_lit 0))

@[expose] noncomputable def sumK (S : Nat → Nat) (k : Nat) : Nat :=
  foldN k (fun s acc => Nat.add acc (S s)) (nat_lit 0)

@[expose] noncomputable def profK (PTB : Nat → Nat) (TOT : Nat) : Bool :=
  allN (nat_lit 32) (fun b => bAnd(allN (nat_lit 5) (fun j =>
      Nat.beq (ent (nat_lit 24) TOT (Nat.add (Nat.mul (nat_lit 6) b) j)) (ent (nat_lit 24) (PTB b) j)),
    Nat.beq (ent (nat_lit 24) TOT (Nat.add (Nat.mul (nat_lit 6) b) (nat_lit 5))) (nat_lit 0)))

@[expose] noncomputable def plB (V r : Nat) : Nat :=
  fld(V, Nat.mul (nat_lit 2048) r, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1))

@[expose] noncomputable def packB (Q : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (Q r) (Nat.mul (nat_lit 2048) r))))
    (nat_lit 11)

@[expose] noncomputable def selB (V : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun s => nIf(f j, Nat.xor s (plB V j), s))) (nat_lit 11)

@[expose] noncomputable def stepB (P V : Nat) : Nat :=
  packB (fun r => Nat.xor (plB V r)
    (selB V (fun j => Nat.beq (Nat.land (Nat.shiftRight (colK P j) r) (nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def nzB (V : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => strictN acc (fun s => Nat.lor s (plB V r))) (nat_lit 11)

@[expose] noncomputable def idB : Nat := packB (fun r => CFSG.KC.F4M3B.pln r (nat_lit 11))

@[expose] noncomputable def ellB : Nat :=
  selB idB (fun j => Nat.beq (Nat.land (Nat.shiftRight (nat_lit 300) j) (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def cntZ (c L Z f : Nat) : Nat :=
  nIf(Nat.beq Z (nat_lit 0), nat_lit 0, strictN (Nat.land Z L) (fun Z1 => Nat.add
    (Nat.shiftLeft (CFSG.KC.popcount Z1 (nat_lit 2048))
      (Nat.mul (nat_lit 24)
        (Nat.add (Nat.mul (nat_lit 6) (Nat.add (nat_lit 1) (Nat.mul (nat_lit 2) c))) f)))
    (Nat.shiftLeft (CFSG.KC.popcount (Nat.xor Z Z1) (nat_lit 2048))
      (Nat.mul (nat_lit 24)
        (Nat.add (Nat.mul (nat_lit 6) (Nat.add (nat_lit 0) (Nat.mul (nat_lit 2) c))) f)))))

@[expose] noncomputable def loopB (E SQ : Nat → Nat) (c L : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun _ _ D _ => cntZ c L D (nat_lit 5))
    (fun _ ih V e D m => nIf(Nat.beq D (nat_lit 0), nat_lit 0, strictN V (fun V' =>
      strictN (nIf(Nat.beq e (nat_lit 0), Nat.xor D (Nat.land D (nzB V')), nat_lit 0)) (fun Z =>
        Nat.add (cntZ c L Z m) (ih (stepB (E e) V') (SQ e) (Nat.xor D Z) (Nat.succ m))))))

@[expose] noncomputable def cntB (E SQ CT : Nat → Nat) (e : Nat) : Nat :=
  strictN (CT e) (fun c => loopB E SQ c ellB (nat_lit 5) idB e
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1)) (nat_lit 0))

@[expose] noncomputable def sliceB (E SQ CT : Nat → Nat) (s : Nat) : Nat :=
  foldN (nat_lit 8) (fun d acc => Nat.add acc (cntB E SQ CT (Nat.add (Nat.mul (nat_lit 8) s) d)))
    (nat_lit 0)

end CFSG.KS.SporSch.C11

end
