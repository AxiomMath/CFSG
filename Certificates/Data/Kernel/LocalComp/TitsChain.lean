module

public import Certificates.Data.Kernel.LocalComp.Tits
public import CFSG.Certificates.Kernel.Lie.CT.Core

public noncomputable section

namespace CFSG.KC.LocalComp.TitsChain

open CFSG.KLie.CT (orN)

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits CFSG.KC.LocalComp.Tits

@[expose] def m11 : Nat := 2047

@[expose] def f16 (R k : Nat) : Nat := pg 16 65535 R k

@[expose] def tupK (c : Nat) (f : Nat → Nat) (t : Nat) : Nat :=
  orN c fun j => Nat.shiftLeft (f (pg 11 m11 t j)) (Nat.mul 11 j)

@[expose] def apL (TL : Nat → Nat) (l x : Nat) : Nat := pg 11 m11 (TL l) x

@[expose] def tupOf (CP : List Nat) : Nat :=
  CP.foldr (fun p acc => Nat.lor p (Nat.shiftLeft acc 11)) 0

@[expose] def invLK (l : Nat) : Nat := nIf(Nat.beq (Nat.land l 1) 0, Nat.succ l, Nat.sub l 1)

@[expose] def levLetters (TL : Nat → Nat) (CP : List Nat) (i : Nat) : List Nat :=
  (List.range 28).filter fun l => (List.range i).all fun t =>
    Nat.beq (apL TL l (CP.getD t 0)) (CP.getD t 0)

@[expose] def walkInvK (c : Nat) (TL : Nat → Nat) (TT : Nat → Nat → Nat) (i : Nat) :
    Nat → Nat → Nat → Nat
  | 0, _, t => t
  | f + 1, k, t => nIf(Nat.beq k 0, t,
      strictN (tupK c (apL TL (invLK (f16 (TT i k) 2))) t) fun t' =>
        walkInvK c TL TT i f (f16 (TT i k) 1) t')

@[expose] def siftK (c : Nat) (TL : Nat → Nat) (TT TS : Nat → Nat → Nat) (sz : Nat → Nat)
    (QT : Nat) : Nat → Nat → Nat → Bool
  | 0, _, t => Nat.beq t QT
  | f + 1, i, t => strictB (f16 (TS i (pg 11 m11 t i)) 0) fun k =>
      bAnd(Nat.blt k (sz i), strictB (walkInvK c TL TT i 64 k t) fun t' =>
        siftK c TL TT TS sz QT f (Nat.succ i) t')

@[expose] def schK (c : Nat) (TL : Nat → Nat) (TT TS TW : Nat → Nat → Nat) (sz : Nat → Nat)
    (QT i l k : Nat) : Bool :=
  strictB (f16 (TS i (apL TL l (f16 (TT i k) 0))) 0) fun ky =>
    bAnd(Nat.blt ky (sz i), strictB (walkInvK c TL TT i 64 ky (tupK c (apL TL l) (TW i k))) fun t =>
      siftK c TL TT TS sz QT (Nat.sub 3 i) (Nat.succ i) t)

@[expose] def schRange (c : Nat) (TL : Nat → Nat) (TT TS TW : Nat → Nat → Nat) (sz : Nat → Nat)
    (QT i : Nat) (ls : List Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun k => bIf(Nat.blt (Nat.add lo k) (sz i),
    ls.all fun l => schK c TL TT TS TW sz QT i l (Nat.add lo k), true)

@[expose] def levelOK (c : Nat) (TL : Nat → Nat) (TT TS TW : Nat → Nat → Nat) (sz : Nat → Nat)
    (CP : List Nat) (i : Nat) : Bool :=
  let ls := levLetters TL CP i
  bAnd(Nat.blt 0 (sz i), bAnd(Nat.ble (sz i) 1755,
  bAnd(Nat.beq (f16 (TT i 0) 0) (CP.getD i 0), bAnd(Nat.beq (TW i 0) (tupOf CP),
  bAnd(allN 1755 (fun p => strictB (f16 (TS i p) 0) fun k =>
    bIf(Nat.blt k (sz i), Nat.beq (f16 (TT i k) 0) p, Nat.beq k 65535)),
    allN (sz i) fun k => strictB (f16 (TT i k) 0) fun p =>
      bAnd(Nat.blt p 1755, bAnd(Nat.beq (f16 (TS i p) 0) k,
      bAnd(ls.all (fun l => Nat.blt (f16 (TS i (apL TL l p)) 0) (sz i)),
        bIf(Nat.beq k 0, true, strictB (f16 (TT i k) 1) fun q => strictB (f16 (TT i k) 2) fun l =>
          bAnd(Nat.blt q k, bAnd(ls.contains l,
          bAnd(Nat.beq (apL TL l (f16 (TT i q) 0)) p,
            Nat.beq (TW i k) (tupK c (apL TL l) (TW i q))))))))))))))

@[expose] def lettersOK (TG TL : Nat → Nat) (words : Array (List Int)) : Bool :=
  bAnd(allN 4 (fun s => permOK 1755 11 m11 (Nat.mul 1755 11) (TG s) (pinvS 1755 11 m11 (TG s))),
    allN words.size (fun j => bAnd(Nat.beq (TL (Nat.mul 2 j)) (wordK 1755 11 TG (words.toList.getD j [])),
      bAnd(Nat.beq (TL (Nat.succ (Nat.mul 2 j))) (pinvS 1755 11 m11 (TL (Nat.mul 2 j))),
        permOK 1755 11 m11 (Nat.mul 1755 11) (TL (Nat.mul 2 j)) (TL (Nat.succ (Nat.mul 2 j)))))))

@[expose] def terminalOK (c : Nat) (TL : Nat → Nat) (CP : List Nat) : Bool :=
  (levLetters TL CP 4).all fun l => Nat.beq (tupK c (apL TL l) (tupOf CP)) (tupOf CP)

@[expose] def spanK (TP : Nat → Nat) (CP : List Nat) (M : Nat → Nat) : Bool :=
  (List.range 52).all fun c =>
    Nat.beq ((List.range CP.length).foldr (fun t acc =>
      nIf(Nat.beq (Nat.land (Nat.shiftRight (M c) t) 1) 1, Nat.xor acc (TP (CP.getD t 0)), acc)) 0)
      (Nat.shiftLeft 1 c)

end CFSG.KC.LocalComp.TitsChain

end
