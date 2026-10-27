module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.AE6F5K

open CFSG.KC.Enum

@[expose] noncomputable def el (T k : Nat) : Nat := fld(T, Nat.mul 48 k, 281474976710655)

@[expose] noncomputable def r16 (D k : Nat) : Nat := fld(D, Nat.mul 16 k, 65535)

@[expose] noncomputable def ap (p i : Nat) : Nat := pg 4 15 p i

@[expose] noncomputable def mulP (p q : Nat) : Nat := pcomp 12 4 15 p q

@[expose] noncomputable def isProd (r p q : Nat) : Bool := allN 12 fun i => Nat.beq (ap r i) (ap p (ap q i))

@[expose] noncomputable def same (p q : Nat) : Bool := allN 12 fun i => Nat.beq (ap p i) (ap q i)

@[expose] noncomputable def treeOK (N T P G NG : Nat) : Bool :=
  bAnd(allN 12 (fun i => Nat.beq (ap (el T 0) i) i),
    allN (Nat.sub N 1) fun j => (fun k =>
      bAnd(Nat.blt (Nat.land (r16 P k) 2047) k, bAnd(Nat.blt (Nat.shiftRight (r16 P k) 11) NG,
        isProd (el T k) (el T (Nat.land (r16 P k) 2047)) (el G (Nat.shiftRight (r16 P k) 11)))))
      (Nat.add j 1))

@[expose] noncomputable def blkS (FP FS t j : Nat) : Nat :=
  pmk 12 4 fun i => Nat.add (Nat.mul 3 fld(FP, Nat.mul 2 (Nat.add (Nat.mul 4 t) (Nat.div i 3)), 3))
    fld(FS, Nat.mul 2 (Nat.add (Nat.mul 3 (Nat.mod (Nat.div j (Nat.pow 6 (Nat.div i 3))) 6))
      (Nat.mod i 3)), 3)

@[expose] noncomputable def invS (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul 4 (ap p i)))) 12

@[expose] noncomputable def powP (u : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) u (fun _ acc => mulP acc u) k

@[expose] noncomputable def w1K (t : Nat) : Bool :=
  bAnd(!(allN 12 fun i => Nat.beq (ap t i) i),
    bAnd(allN 12 (fun i => Nat.beq (ap t (ap t (ap t i))) i),
      bAnd(allN 12 (fun i => Nat.beq (Nat.div (ap t i) 3) (Nat.div i 3)),
        !(allN 4 fun b => !(allN 12 fun i => Nat.beq (Nat.div i 3) b || Nat.beq (ap t i) i)))))

@[expose] noncomputable def entryOK (G CT HT s e : Nat) : Bool :=
  cond (Nat.blt e 32768)
    ((fun x c m => bAnd(Nat.blt x 7, bAnd(Nat.blt c 216, bAnd(Nat.blt 0 m,
      (fun si => bAnd(permOK 12 4 15 48 s si,
        w1K (powP (mulP s (mulP (el G x) (mulP si (el CT c)))) (Nat.sub m 1)))) (invS s)))))
      (Nat.land e 7) (Nat.land (Nat.shiftRight e 3) 255) (Nat.shiftRight e 11))
    bAnd(Nat.blt (Nat.sub e 32768) 1296, same s (el HT (Nat.sub e 32768)))

@[expose] noncomputable def piOK (G CT HT FP FS t D : Nat) : Bool :=
  allN 1296 fun j => entryOK G CT HT (blkS FP FS t j) (r16 D j)

end CFSG.KC.AE6F5K
