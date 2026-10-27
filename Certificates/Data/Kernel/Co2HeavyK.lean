module

public import Certificates.Data.Kernel.Co2InvS
public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Co2HeavyK

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KS CFSG.KC.M1F2
open CFSG.KC.Enum (pg)

@[expose] noncomputable def wAt (W : Nat → Nat) (i : Nat) : Nat :=
  fld(W (Nat.shiftRight i (nat_lit 6)), Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 128),
    nat_lit 340282366920938463463374607431768211455)

@[expose] noncomputable def pOf (w : Nat) : Nat := fld(w, nat_lit 0, nat_lit 262143)

@[expose] noncomputable def t1Of (w : Nat) : Nat := fld(w, nat_lit 18, nat_lit 1)

@[expose] noncomputable def t2Of (w : Nat) : Nat := fld(w, nat_lit 19, nat_lit 1)

@[expose] noncomputable def cjOf (w : Nat) : Nat := fld(w, nat_lit 20, nat_lit 262143)

@[expose] noncomputable def jOf (w : Nat) : Nat := fld(w, nat_lit 38, nat_lit 63)

@[expose] noncomputable def maOf (w : Nat) : Nat := fld(w, nat_lit 44, nat_lit 8191)

@[expose] noncomputable def mbOf (w : Nat) : Nat := fld(w, nat_lit 57, nat_lit 8191)

@[expose] noncomputable def commK (X Y : Nat) : Bool := Nat.beq (mulV X Y) (mulV Y X)

@[expose] noncomputable def conjK (S X R : Nat) : Bool := Nat.beq (mulV S X) (mulV R S)

@[expose] noncomputable def bindK (CF SQ W CA : Nat → Nat) (i : Nat) : Bool :=
  letB (pOf (wAt W i)) fun p =>
    andK (Nat.beq (SQ i) (elemAt CF p)) (
    andK (Nat.beq (mulV (SQ i) (SQ i)) IDP) (
    andK (implK (Nat.blt (Nat.succ i) (nat_lit 6144)) (Nat.blt p (pOf (wAt W (Nat.succ i))))) (
    andK (Nat.ble (CA (Nat.shiftRight p (nat_lit 12))) i)
      (Nat.blt i (CA (Nat.succ (Nat.shiftRight p (nat_lit 12))))))))

@[expose] noncomputable def caK (CA : Nat → Nat) : Bool :=
  andK (Nat.beq (CA (nat_lit 0)) (nat_lit 0)) (Nat.beq (CA (nat_lit 64)) (nat_lit 6144))

@[expose] noncomputable def sq01 (CF : Nat → Nat) (k : Nat) : Nat :=
  strictN (elemAt CF k) fun X => nIf(Nat.beq (mulV X X) IDP, nat_lit 1, nat_lit 0)

@[expose] noncomputable def chunkK (CF CA : Nat → Nat) (c : Nat) : Bool :=
  andK (Nat.ble (CA c) (CA (Nat.succ c)))
    (Nat.beq (sumBelow (nat_lit 4096) (nat_lit 64)
        (fun t => sq01 CF (Nat.add (Nat.mul (nat_lit 4096) c) t)))
      (Nat.sub (CA (Nat.succ c)) (CA c)))

@[expose] noncomputable def cnt1 (SQ : Nat → Nat) (X : Nat) : Nat :=
  sumBelow (nat_lit 6144) (nat_lit 96) fun i => nIf(commK (SQ i) X, nat_lit 1, nat_lit 0)

@[expose] noncomputable def cnt2 (SQ W : Nat → Nat) (X : Nat) : Nat :=
  sumBelow (nat_lit 6144) (nat_lit 96) fun i =>
    nIf(Nat.beq (t1Of (wAt W i)) (nat_lit 1), nIf(commK (SQ i) X, nat_lit 1, nat_lit 0), nat_lit 0)

@[expose] noncomputable def part1K (CF SQ RP : Nat → Nat) (j : Nat) : Bool :=
  andK (Nat.blt (RP j) (nat_lit 262144))
    (Nat.blt (strictN (elemAt CF (RP j)) fun X => cnt1 SQ X) (nat_lit 1024))

@[expose] noncomputable def part2K (CF SQ W RP : Nat → Nat) (j : Nat) : Bool :=
  andK (Nat.blt (RP (Nat.add (nat_lit 31) j)) (nat_lit 262144))
    (Nat.blt (strictN (elemAt CF (RP (Nat.add (nat_lit 31) j))) fun X => cnt2 SQ W X)
      (nat_lit 1024))

@[expose] noncomputable def witK (CF SQ W RP : Nat → Nat) (i : Nat) : Bool :=
  letB (wAt W i) fun w =>
    bIf(Nat.beq (t1Of w) (nat_lit 0),
      andK (Nat.blt (jOf w) (nat_lit 31))
        (conjK (elemAt CF (cjOf w)) (SQ i) (elemAt CF (RP (jOf w)))),
      bIf(Nat.beq (t2Of w) (nat_lit 0),
        andK (Nat.blt (jOf w) (nat_lit 17))
          (conjK (elemAt CF (cjOf w)) (SQ i) (elemAt CF (RP (Nat.add (nat_lit 31) (jOf w))))),
        true))

@[expose] noncomputable def inL2K (W : Nat → Nat) (a : Nat) : Bool :=
  andK (Nat.blt a (nat_lit 6144)) (letB (wAt W a) fun w =>
    andK (Nat.beq (t1Of w) (nat_lit 1)) (Nat.beq (t2Of w) (nat_lit 1)))

@[expose] noncomputable def l2K (W : Nat → Nat) : Bool :=
  Nat.beq (sumBelow (nat_lit 6144) (nat_lit 96) fun i => nIf(inL2K W i, nat_lit 1, nat_lit 0))
    (nat_lit 1024)

@[expose] noncomputable def normK (SQ W : Nat → Nat) (A B i : Nat) : Bool :=
  implK (inL2K W i) (letB (wAt W i) fun w =>
    andK (inL2K W (maOf w)) (
    andK (Nat.beq (mulV A (SQ i)) (mulV (SQ (maOf w)) A)) (
    andK (inL2K W (mbOf w)) (Nat.beq (mulV B (SQ i)) (mulV (SQ (mbOf w)) B)))))

@[expose] def m22RelsK : List (List (Nat × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, false),
      (1, true)],
    [(0, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true),
      (0, false), (1, false)],
    [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true),
      (1, true), (1, true), (1, true)]]

@[expose] noncomputable def letterP (A B Ai Bi : Nat) (l : Nat × Bool) : Nat :=
  selN (Nat.beq l.1 (nat_lit 0)) (selN l.2 A Ai) (selN l.2 B Bi)

@[expose] noncomputable def wordP (A B Ai Bi : Nat) (w : List (Nat × Bool)) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulV acc (letterP A B Ai Bi l)) fun acc' => ih acc') w acc

@[expose] noncomputable def invK (A B Ai Bi : Nat) : Bool :=
  andK (Nat.beq (mulV A Ai) IDP) (andK (Nat.beq (mulV B Bi) IDP) (notK (Nat.beq B IDP)))

@[expose] noncomputable def relK (A B Ai Bi : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ acc => andK (Nat.beq (wordP A B Ai Bi w IDP) IDP) acc) m22RelsK

@[expose] noncomputable def mvecK (VP T PT i : Nat) : Bool :=
  andK (Nat.blt (pg 12 (mask 12) PT i) (nat_lit 2300))
    (Nat.beq (vmF 22 T (pg 22 (mask 22) VP i)) (pg 22 (mask 22) VP (pg 12 (mask 12) PT i)))

end CFSG.KC.Co2HeavyK

end
