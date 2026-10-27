module

public import Certificates.Data.Kernel.O8.Core
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def row12 (a i : Nat) : Nat := fget a i (nat_lit 12)

@[expose] noncomputable def low12 : Nat := nat_lit 5445847423328601499764522166702896582657

@[expose] noncomputable def mul12K (a b : Nat) : Nat :=
  strictN a fun a => strictN b fun b =>
    xorN (nat_lit 12) fun l => Nat.land
      (Nat.mul (Nat.land (Nat.shiftRight a l) low12) (nat_lit 4095)) (Nat.mul (row12 b l) low12)

@[expose] noncomputable def mulVec12K (k v : Nat) : Nat :=
  strictN k fun k => strictN v fun v =>
    orN (nat_lit 12) fun i =>
      Nat.shiftLeft (Nat.mod (popc (nat_lit 12) (Nat.land (row12 k i) v)) (nat_lit 2)) i

@[expose] noncomputable def unpackL (x : Nat) : List Nat :=
  (List.range (Nat.mod x (nat_lit 16))).map fun j =>
    fget (Nat.shiftRight x (nat_lit 4)) j (nat_lit 12)

@[expose] noncomputable def ID12 : Nat := orN (nat_lit 12) fun i => pw2 (Nat.mul (nat_lit 13) i)

@[expose] noncomputable def kron6K (R : Nat → Nat) : Nat :=
  orN (nat_lit 12) fun r => Nat.shiftLeft
    (orN (nat_lit 6) fun q => nIf(Nat.beq (bitN (R (Nat.div r (nat_lit 2))) q) (nat_lit 1),
      pw2 (Nat.add (Nat.mul (nat_lit 2) q) (Nat.mod r (nat_lit 2))), nat_lit 0))
    (Nat.mul (nat_lit 12) r)

@[expose] noncomputable def vKey (V : Nat) : Nat := Nat.land V (maskN (nat_lit 144))
@[expose] noncomputable def vPar (V : Nat) : Nat :=
  fget (Nat.shiftRight V (nat_lit 144)) 0 (nat_lit 17)
@[expose] noncomputable def vGen (V : Nat) : Nat :=
  fget (Nat.shiftRight V (nat_lit 161)) 0 (nat_lit 5)
@[expose] noncomputable def vDep (V : Nat) : Nat :=
  fget (Nat.shiftRight V (nat_lit 166)) 0 (nat_lit 8)
@[expose] noncomputable def vCl (V j : Nat) : Nat :=
  fget (Nat.shiftRight V (nat_lit 174)) j (nat_lit 17)

@[expose] noncomputable def enKey (D : Nat → Nat) (i : Nat) : Nat := vKey (D i)
@[expose] noncomputable def enPar (D : Nat → Nat) (i : Nat) : Nat := vPar (D i)
@[expose] noncomputable def enGen (D : Nat → Nat) (i : Nat) : Nat := vGen (D i)
@[expose] noncomputable def enDep (D : Nat → Nat) (i : Nat) : Nat := vDep (D i)

@[expose] noncomputable def enFind (D : Nat → Nat) (k : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih lo hi => nIf(Nat.blt lo hi,
      strictN (Nat.div (Nat.add lo hi) (nat_lit 2)) fun mid => strictN (enKey D mid) fun K =>
        nIf(Nat.beq K k, nat_lit 1, nIf(Nat.blt K k, ih (Nat.succ mid) hi, ih lo mid)),
      nat_lit 0)) fuel

@[expose] noncomputable def enMemK (D : Nat → Nat) (m k : Nat) : Bool :=
  Nat.beq (enFind D k (nat_lit 18) (nat_lit 0) m) (nat_lit 1)

@[expose] noncomputable def enNotMemK (D : Nat → Nat) (m k : Nat) : Bool :=
  allN m fun i => notB (Nat.beq (enKey D i) k)

@[expose] noncomputable def enumHeadOK (G GI : Nat → Nat) (ng m : Nat) (D : Nat → Nat) (z : Nat) :
    Bool :=
  andB (allN ng fun j =>
      andB (Nat.beq (mul12K (G j) (GI j)) ID12) (Nat.beq (mul12K (GI j) (G j)) ID12))
    (andB (Nat.blt z m) (Nat.beq (enKey D z) ID12))

@[expose] noncomputable def enumBlockOK (G : Nat → Nat) (ng m : Nat) (D : Nat → Nat) (b : Nat) :
    Bool :=
  allN (nat_lit 256) fun k => (fun i => orB (notB (Nat.blt i m)) (Nat.beq (nat_lit 1)
      (strictN (D i) fun V => strictN (vKey V) fun K => strictN (D (vPar V)) fun W =>
        nIf(andB
          (orB (Nat.beq K ID12) (andB (Nat.blt (vPar V) m) (andB (Nat.blt (vGen V) ng)
            (andB (Nat.blt (vDep W) (vDep V)) (Nat.beq K (mul12K (vKey W) (G (vGen V))))))))
          (andB (allN ng fun j => andB (Nat.blt (vCl V j) m)
              (Nat.beq (enKey D (vCl V j)) (mul12K K (G j))))
            (orB (notB (Nat.blt (Nat.succ i) m)) (Nat.blt K (enKey D (Nat.succ i))))),
          nat_lit 1, nat_lit 0))))
    (Nat.add (Nat.mul (nat_lit 256) b) k)

end CFSG.KC.O8

end
