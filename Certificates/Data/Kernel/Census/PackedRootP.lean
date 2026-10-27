module

public import Certificates.Data.Kernel.Census.PackedRootBit
public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

@[expose] def encE (x : Nat × Nat × Nat × Nat) : Nat :=
  Nat.add x.1 (Nat.shiftLeft (Nat.add x.2.1 (Nat.shiftLeft (Nat.add x.2.2.1
    (Nat.shiftLeft x.2.2.2 (nat_lit 32))) (nat_lit 32))) (nat_lit 32))

@[expose] def packB : List (Nat × Nat × Nat × Nat) → Nat
  | [] => 0
  | x :: l => Nat.add (encE x) (Nat.shiftLeft (packB l) (nat_lit 128))

@[expose] def decE (P k : Nat) : Nat × Nat × Nat × Nat :=
  (fld(P, Nat.shiftLeft k (nat_lit 7), nat_lit 4294967295),
    fld(P, Nat.add (Nat.shiftLeft k (nat_lit 7)) (nat_lit 32), nat_lit 4294967295),
    fld(P, Nat.add (Nat.shiftLeft k (nat_lit 7)) (nat_lit 64), nat_lit 4294967295),
    fld(P, Nat.add (Nat.shiftLeft k (nat_lit 7)) (nat_lit 96), nat_lit 4294967295))

@[expose] def fitsB (bs : List (Array (Nat × Nat × Nat × Nat))) : Bool :=
  bs.all fun b => b.toList.all fun x =>
    Nat.blt x.1 (nat_lit 4294967296) && Nat.blt x.2.1 (nat_lit 4294967296) &&
      Nat.blt x.2.2.1 (nat_lit 4294967296) && Nat.blt x.2.2.2 (nat_lit 4294967296)

@[expose] def ugetP : List Nat → List Nat → Nat → Nat × Nat × Nat × Nat
  | P :: Ps, s :: Ss, k => bif Nat.blt k s then decE P k else ugetP Ps Ss (Nat.sub k s)
  | _, _, _ => default

@[expose] noncomputable def withPacked {β : Sort _} (bs : List (Array (Nat × Nat × Nat × Nat)))
    (k : List Nat → List Nat → β) : β :=
  strictLA (bs.map fun b => packB b.toList) fun Ps => strictLA (bs.map Array.size) fun Ss => k Ps Ss

section Checks

variable (n w : Nat)

@[expose] noncomputable def puAtFG (E : Nat → Nat × Nat × Nat × Nat) (r : RootConjP) :
    Nat → Nat → Nat → Nat :=
  fun f => Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih k p =>
      let e := E k
      bif Nat.beq e.1 0 then ppcAt w r.xs e.2.1 p else
        at' w r.xs[e.2.2.1]! (ih e.2.1 (at' w r.xi[e.2.2.1]! p))) f

@[expose] noncomputable def pkeyUG (E : Nat → Nat × Nat × Nat × Nat) (r : RootConjP) (k : Nat) :
    Nat :=
  Nat.ofDigits n (r.kb.map (fun p => puAtFG w E r ((E k).2.2.2 + 1) k p))

@[expose] noncomputable def pentryOKBG (E : Nat → Nat × Nat × Nat × Nat) (U : Nat)
    (inX : Nat → Bool) (bmode : Nat) (skip : List Nat) (pG : Array (Array Nat)) (k : Nat)
    (r : RootConjP) (j : Nat) : Bool :=
  let e := E j
  bif Nat.beq e.1 0 then
    Nat.beq e.2.2.2 0 && pinvol n w (ppcA n w r.xs e.2.1) && Nat.blt e.2.2.1 r.cands.size &&
      pleafOKB n w inX bmode skip r.x r.ga r.gi pG (Nat.land (Nat.shiftRight e.2.1 k) 1)
        (ppcA n w r.xs e.2.1) (r.cands.toList.getD e.2.2.1 default)
  else
    Nat.blt e.2.1 U && Nat.beq e.2.2.2 ((E e.2.1).2.2.2 + 1) && Nat.blt e.2.2.1 r.xs.length

@[expose] noncomputable def pordBlkP (r : RootConjP) (a len : Nat) : Bool :=
  withPacked r.ukc fun Ps Ss => (List.range' a len).all fun i =>
    Nat.blt (pkeyUG n w (ugetP Ps Ss) r i) (pkeyUG n w (ugetP Ps Ss) r (i + 1))

@[expose] noncomputable def pentBlkP (U : Nat) (inX : Nat → Bool) (skip : List Nat)
    (pG : Array (Array Nat)) (k : Nat) (r : RootConjP) (a len : Nat) : Bool :=
  withPacked r.ukc fun Ps Ss => (List.range' a len).all fun j =>
    bAnd(pentryOKBG n w (ugetP Ps Ss) U inX 2 skip pG k r j,
      pentryOKBG n w (ugetP Ps Ss) U inX 1 skip pG k r j)

end Checks

end CFSG.KC.Census
