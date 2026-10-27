module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.QuandleCheck

public section

namespace CFSG.KD.MinusQuandle

open CFSG.OddTranspositions.PartThree

@[expose] def force {β : Sort _} (y : ℕ) (k : ℕ → β) : β :=
  Nat.rec (motive := fun _ => β) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] def lane (w n j : ℕ) : ℕ := Nat.land (Nat.shiftRight n (w * j)) (2 ^ w - 1)

@[expose] def tq (R : ℕ → ℕ) (i j : ℕ) : ℕ := lane 7 (R i) j

@[expose] def dq (D : ℕ → ℕ) (a t : ℕ) : ℕ := lane 16 (D a) t

@[expose] def rowsOK (R : ℕ → ℕ) : Bool :=
  (List.range 65).all fun i =>
    (List.range 65).map (tq R i) == (minusTable[i]!).toList &&
      (List.range 65).all fun j => tq R i j < 65

@[expose] def derivOK (D : ℕ → ℕ) : Bool :=
  (List.range 65).all fun a => (List.range 65).map (dq D a) == (minusQuandleDeriv[a]!).toList

@[expose] def seedT (a : ℕ) : ℕ := minusQuandleSeed[a]!

@[expose] def forced (R D : ℕ → ℕ) (a c : ℕ) : ℕ :=
  (List.range 65).foldl (fun acc t => force acc fun acc =>
    let p := dq D a t % 65
    let code := dq D a t / 65
    let v := if code == 0 then p else if code == 1 then c else
      tq R (lane 7 acc (dq D a ((code - 2) / 65) % 65)) (lane 7 acc (dq D a ((code - 2) % 65) % 65))
    acc ||| (v <<< (7 * p))) 0

@[expose] def recOK (R D : ℕ → ℕ) (a c d : ℕ) : Bool :=
  (List.range 65).all fun t =>
    let p := dq D a t % 65
    let code := dq D a t / 65
    lane 7 d p < 65 &&
    lane 7 d p == (if code == 0 then p else if code == 1 then c else
      tq R (lane 7 d (dq D a ((code - 2) / 65) % 65)) (lane 7 d (dq D a ((code - 2) % 65) % 65)))

@[expose] def badT (R : ℕ → ℕ) (d : ℕ) : Bool :=
  (List.range 65).any fun i => (List.range 65).any fun j =>
    lane 7 d (tq R i j) != tq R (lane 7 d i) (lane 7 d j)

@[expose] def perpA (R D : ℕ → ℕ) (a : ℕ) : Bool :=
  seedT a < 65 &&
  (List.range 65).all (fun i => (List.range 65).all fun j =>
    !(i < j) || dq D a i % 65 != dq D a j % 65) &&
  (List.range 65).all (fun t =>
    let p := dq D a t % 65
    let code := dq D a t / 65
    if code == 0 then tq R a p == p
    else if code == 1 then p == seedT a
    else (code - 2) / 65 < t && (code - 2) % 65 < t &&
      tq R (dq D a ((code - 2) / 65) % 65) (dq D a ((code - 2) % 65) % 65) == p) &&
  (List.range 65).all fun c =>
    c == seedT a || c == tq R a (seedT a) ||
      force (forced R D a c) fun d => recOK R D a c d && badT R d

@[expose] def perpOK (R D : ℕ → ℕ) (lo hi : ℕ) : Bool :=
  ((List.range (hi - lo)).map (· + lo)).all (perpA R D)

@[expose] def orF (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor (f k) acc) n

@[expose] def allF (n : ℕ) (g : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => Bool.rec (motive := fun _ => Bool) false acc (g k)) n

@[expose] def imgS (R : ℕ → ℕ) (j S : ℕ) : ℕ :=
  force (R j) fun r => orF 65 fun i => Nat.shiftLeft (lane 4225 S i) (Nat.mul 4225 (lane 7 r i))

@[expose] def stepS (R : ℕ → ℕ) (S : ℕ) : ℕ :=
  force S fun S => Nat.lor S (orF 65 fun j => force (imgS R j S) fun I =>
    force (orF 65 fun y => lane 4225 (Nat.land I S) y) fun N =>
      Nat.land I (orF 65 fun y => Nat.shiftLeft N (Nat.mul 4225 y)))

@[expose] def colS : ℕ := orF 65 fun k => Nat.shiftLeft 1 (Nat.mul 65 k)

@[expose] def diagS : ℕ := orF 65 fun k => Nat.shiftLeft 1 (Nat.mul 66 k)

@[expose] def initS : ℕ := force colS fun c => orF 65 fun x =>
  Nat.shiftLeft (Nat.lor (Nat.shiftLeft (2 ^ 65 - 1) (Nat.mul 65 x)) (Nat.shiftLeft c x))
    (Nat.mul 4225 x)

@[expose] def primS (R : ℕ → ℕ) : Bool :=
  force (stepS R (stepS R initS)) fun S => force diagS fun d =>
    allF 65 fun x => Nat.beq (Nat.lor (lane 4225 S x) d) (2 ^ 4225 - 1)

end CFSG.KD.MinusQuandle
