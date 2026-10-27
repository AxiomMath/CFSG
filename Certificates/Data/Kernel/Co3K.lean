module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Co3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def pk (p q : Nat) : Nat := pcomp (nat_lit 276) (nat_lit 9) (mask 9) p q

@[expose] noncomputable def idk : Nat := pidn (nat_lit 276) (nat_lit 9)

@[expose] noncomputable def anyNK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def prod3K (LR TR : Nat → Nat) (P : Nat → Bool) (a : Nat) : Bool :=
  strictB (LR (nat_lit 0)) (fun R0 => strictB (LR (nat_lit 1)) (fun R1 =>
  strictB (LR (nat_lit 2)) (fun R2 =>
  strictB (TR (Nat.add (roff (nat_lit 276) (nat_lit 2484) R0) a)) (fun ta =>
  allN (rcnt R1) (fun b => strictB (pk ta (TR (Nat.add (roff (nat_lit 276) (nat_lit 2484) R1) b)))
    (fun tab =>
  allN (rcnt R2) (fun c => strictB (pk tab (TR (Nat.add (roff (nat_lit 276) (nat_lit 2484) R2) c)))
    P)))))))

@[expose] noncomputable def eK (E EZ G : Nat) : Bool :=
  strictB (pk G E) (fun GE => bIf(Nat.beq GE (pk E G), true, Nat.beq GE (pk EZ G)))

@[expose] noncomputable def k3K (S SI D : Nat → Nat) (G : Nat) : Bool :=
  bIf(Nat.beq (pk G G) idk,
    bIf(Nat.beq G idk, true,
      bIf(allN (nat_lit 8) (fun k => strictB (pk (pk (S k) G) (SI k)) (fun C =>
          Nat.beq (pk G C) (pk C G))),
        anyNK (nat_lit 23) (fun i => Nat.beq G (D i)), true)),
    true)

@[expose] noncomputable def lane (T k : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul k (nat_lit 2484))) (mask (nat_lit 2484))

@[expose] noncomputable def packL (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.lor ih (Nat.shiftLeft (f k) (Nat.mul k (nat_lit 2484)))) n

@[expose] noncomputable def powK (X k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idk (fun _ ih => pk X ih) k

@[expose] noncomputable def wK (S SI : Nat → Nat) (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 64),
    pk (pk (pk (S (Nat.land k (nat_lit 7))) (S (Nat.shiftRight k (nat_lit 3))))
      (SI (Nat.land k (nat_lit 7)))) (SI (Nat.shiftRight k (nat_lit 3))),
    powK (S (Nat.sub k (nat_lit 64))) (nat_lit 4))

@[expose] noncomputable def sepK (X Y W : Nat) : Bool :=
  bIf(Nat.beq (pk W X) (pk X W), bIf(Nat.beq (pk W Y) (pk Y W), false, true), true)

@[expose] noncomputable def pairK (T Z X Y : Nat) : Bool :=
  bIf(Nat.beq (pk X Y) (pk Y X),
    bIf(Nat.beq X Z, true, bIf(Nat.beq Y Z, true, bIf(Nat.beq Y X, true,
      bIf(Nat.beq Y (pk X Z), true,
        anyNK (nat_lit 72) (fun k => strictB (lane T k) (fun W => sepK X Y W)))))),
    true)

@[expose] noncomputable def k5RowK (D : Nat → Nat) (T Z i : Nat) : Bool :=
  strictB (D i) (fun X => allN (nat_lit 23) (fun j => strictB (D j) (fun Y => pairK T Z X Y)))

@[expose] noncomputable def fix1K (K : Nat) : Bool :=
  anyNK (nat_lit 36) (fun p => allN (nat_lit 36) (fun i =>
    Bool.rec (Bool.rec true false (Nat.beq i p)) (Nat.beq i p)
      (Nat.beq (pg (nat_lit 6) (mask 6) K i) i)))

end CFSG.KC.Co3K

end
