module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.FixBoundK

@[expose] noncomputable def par24 (x : Nat) : Nat :=
  (fun c => Nat.land (Nat.xor c (Nat.xor (Nat.shiftRight c (nat_lit 1))
      (Nat.shiftRight c (nat_lit 2)))) (nat_lit 1))
    ((fun b => Nat.xor b (Nat.shiftRight b (nat_lit 3)))
      ((fun a => Nat.xor a (Nat.shiftRight a (nat_lit 6)))
        ((fun y => Nat.xor y (Nat.shiftRight y (nat_lit 12)))
          (Nat.land x (nat_lit 16777215)))))

@[expose] noncomputable def lenS {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def appS (l₁ l₂ : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) l₂ (fun x _ ih => x :: ih) l₁

@[expose] noncomputable def nthS {α : Type} (d : α) (l : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih n => Nat.rec (motive := fun _ => α) x (fun k _ => ih k) n) l

@[expose] noncomputable def allS {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def selS (l : List Nat) (s : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih s =>
      Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat) (ih (Nat.shiftRight s (nat_lit 1)))
          (x :: ih (Nat.shiftRight s (nat_lit 1))) (Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1)))
        [] (Nat.beq s (nat_lit 0)))
    l s

@[expose] noncomputable def popS (l : List Nat) (A : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ _ ih A => nIf(Nat.beq A (nat_lit 0), nat_lit 0,
      Nat.add (Nat.land A (nat_lit 1)) (ih (Nat.shiftRight A (nat_lit 1)))))
    l A

@[expose] noncomputable def zS (bs : List Nat) (A acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun b _ ih A acc => nIf(Nat.beq A (nat_lit 0), acc,
      ih (Nat.shiftRight A (nat_lit 1))
        (nIf(Nat.beq (Nat.land A (nat_lit 1)) (nat_lit 1), Nat.land acc b, acc))))
    bs A acc

@[expose] noncomputable def rowS (f i : Nat) (ws : List Nat) (j₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih j => bAnd(Nat.beq (par24 (Nat.land f w)) (nIf(Nat.beq i j, nat_lit 1, nat_lit 0)),
      ih (Nat.succ j)))
    ws j₀

@[expose] noncomputable def dualS (ws fs : List Nat) (i₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (lenS ws))
    (fun f _ ih i => bAnd(rowS f i ws (nat_lit 0), ih (Nat.succ i)))
    fs i₀

@[expose] noncomputable def rankK (ws fs : List Nat) (lhs : Nat) : Bool :=
  bAnd(dualS ws fs (nat_lit 0),
    Nat.ble lhs (Nat.mul (nat_lit 16384) (Nat.pow (nat_lit 2) (lenS ws))))

@[expose] noncomputable def memZ (r : Nat) (F Mws : List Nat) (full A Z sF : Nat) (fs : List Nat) :
    Bool :=
  bAnd(Nat.beq (Nat.land A full) A,
  bAnd(Nat.beq (Nat.land sF (Nat.lor A Z)) sF,
    rankK (appS Mws (selS F sF)) fs
      (Nat.mul (Nat.mul (Nat.mul (popS F A) (Nat.pow (nat_lit 2) r)) (nat_lit 2048)) (popS F Z))))

@[expose] noncomputable def memberK (r : Nat) (F bs Mws : List Nat) (full A sF : Nat)
    (fs : List Nat) : Bool :=
  memZ r F Mws full A (zS bs A full) sF fs

@[expose] noncomputable def omegaK (r : Nat) (F Mws : List Nat) (full sF : Nat) (fs : List Nat) :
    Bool :=
  bAnd(Nat.beq (Nat.land sF full) sF,
    rankK (appS Mws (selS F sF)) fs
      (Nat.mul (Nat.mul (Nat.mul (nat_lit 2) (Nat.pow (nat_lit 2) r)) (nat_lit 2048)) (lenS F)))

abbrev Rep := Nat × List Nat × List Nat × List Nat × Nat × List Nat

abbrev Mem := Nat × Nat × List Nat

@[expose] noncomputable def repFull (p : Rep) (full : Nat) : Bool :=
  omegaK p.1 p.2.1 p.2.2.2.1 full p.2.2.2.2.1 p.2.2.2.2.2

@[expose] noncomputable def repK (p : Rep) : Bool :=
  repFull p (Nat.sub (Nat.pow (nat_lit 2) (lenS p.2.1)) (nat_lit 1))

@[expose] noncomputable def chunkFull (p : Rep) (full : Nat) (ms : List Mem) : Bool :=
  allS (fun e => memberK p.1 p.2.1 p.2.2.1 p.2.2.2.1 full e.1 e.2.1 e.2.2) ms

@[expose] noncomputable def chunkK (p : Rep) (ms : List Mem) : Bool :=
  chunkFull p (Nat.sub (Nat.pow (nat_lit 2) (lenS p.2.1)) (nat_lit 1)) ms

@[expose] noncomputable def repD : Rep := (nat_lit 0, [], [], [], nat_lit 0, [])

@[expose] noncomputable def repAt (reps : List Rep) (i : Nat) : Bool := repK (nthS repD reps i)

@[expose] noncomputable def chAt (reps : List Rep) (ch : List (Nat × List Mem)) (k : Nat) : Bool :=
  (fun c : Nat × List Mem => chunkK (nthS repD reps c.1) c.2) (nthS (nat_lit 0, []) ch k)

end CFSG.KC.FixBoundK

end
