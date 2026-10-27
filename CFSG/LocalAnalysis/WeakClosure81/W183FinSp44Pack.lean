module

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

@[expose] def gmul (a b : Nat) : Nat :=
  let r := (if b &&& 1 = 1 then a else 0) ^^^ (if b &&& 2 = 2 then a <<< 1 else 0)
  if r &&& 4 = 4 then r ^^^ 7 else r

@[expose] def mulW (b : Nat) : Nat :=
  let lo := b &&& 0x55
  let hi := (b >>> 1) &&& 0x55
  hi ||| ((lo ^^^ hi) <<< 1)

@[expose] def scal (a b : Nat) : Nat :=
  if a = 0 then 0 else if a = 1 then b else if a = 2 then mulW b else b ^^^ mulW b

@[expose] def row (M i : Nat) : Nat := (M >>> (8 * i)) &&& 255

@[expose] def ent (r k : Nat) : Nat := (r >>> (2 * k)) &&& 3

@[expose] def e2 (M i j : Nat) : Nat := (M >>> (2 * (4 * i + j))) &&& 3

@[expose] def mulRow (r B : Nat) : Nat :=
  scal (ent r 0) (row B 0) ^^^ scal (ent r 1) (row B 1) ^^^ scal (ent r 2) (row B 2) ^^^
    scal (ent r 3) (row B 3)

@[expose] def mmul (A B : Nat) : Nat :=
  mulRow (row A 0) B ||| (mulRow (row A 1) B <<< 8) ||| (mulRow (row A 2) B <<< 16) |||
    (mulRow (row A 3) B <<< 24)

@[expose] def transp (M : Nat) : Nat :=
  (List.range 4).foldl (fun acc i => (List.range 4).foldl (fun acc j =>
    acc ||| (((M >>> (2 * (4 * i + j))) &&& 3) <<< (2 * (4 * j + i)))) acc) 0

@[expose] def idM : Nat := 1 + 1024 + 1048576 + 1073741824

@[expose] def Jm : Nat := 64 + 4096 + 262144 + 16777216

@[expose] def symp (g : Nat) : Bool := mmul (mmul (transp g) Jm) g == Jm

@[expose] def idxA : Nat → Nat × Nat
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (1, 3) | _ => (2, 3)

@[expose] def rho (g : Nat) : Nat :=
  let ent' : Nat → Nat → Nat := fun A B =>
    let i := (idxA A).1; let j := (idxA A).2; let k := (idxA B).1; let l := (idxA B).2
    gmul (e2 g i k) (e2 g j l) ^^^ gmul (e2 g i l) (e2 g j k)
  (ent' 0 0) ||| (ent' 0 1 <<< 2) ||| (ent' 0 2 <<< 4) ||| (ent' 0 3 <<< 6) |||
  (ent' 1 0 <<< 8) ||| (ent' 1 1 <<< 10) ||| (ent' 1 2 <<< 12) ||| (ent' 1 3 <<< 14) |||
  (ent' 2 0 <<< 16) ||| (ent' 2 1 <<< 18) ||| (ent' 2 2 <<< 20) ||| (ent' 2 3 <<< 22) |||
  (ent' 3 0 <<< 24) ||| (ent' 3 1 <<< 26) ||| (ent' 3 2 <<< 28) ||| (ent' 3 3 <<< 30)

@[expose] def rhoPow : Nat → Nat → Nat
  | 0, g => g
  | n + 1, g => rhoPow n (rho g)

@[expose] def uMat (a b c d : Nat) : Nat :=
  let p : Nat → Nat → Nat → Nat := fun i j v => v <<< (2 * (4 * i + j))
  p 0 0 1 ||| p 0 1 a ||| p 0 2 b ||| p 0 3 c |||
  p 1 1 1 ||| p 1 2 d ||| p 1 3 (b ^^^ gmul a d) |||
  p 2 2 1 ||| p 2 3 a ||| p 3 3 1

abbrev El : Type := Nat × Nat

@[expose] def oneE : El := (idM, 0)

@[expose] def gmulE (x y : El) : El := (mmul x.1 (rhoPow x.2 y.1), (x.2 + y.2) % 4)

@[expose] def invE (x : El) : El :=
  let j' := (4 - x.2) % 4
  (rhoPow j' (mmul Jm (mmul (transp x.1) Jm)), j')

@[expose] def conjE (g x : El) : El := gmulE g (gmulE x (invE g))

@[expose] def powE : Nat → El → El
  | 0, _ => oneE
  | n + 1, x => gmulE x (powE n x)

@[expose] def validB (x : El) : Bool := decide (x.1 < 4294967296) && symp x.1 && decide (x.2 < 4)

@[expose] def Pel : List El :=
  (List.range 4).flatMap fun a => (List.range 4).flatMap fun b =>
    (List.range 4).flatMap fun c => (List.range 4).flatMap fun d =>
      (List.range 4).map fun j => (uMat a b c d, j)

@[expose] def invs : List El := Pel.filter fun x => x ≠ oneE && gmulE x x == oneE

@[expose] def invsA : Array El := invs.toArray

@[expose] def n127 : Nat := invs.length

@[expose] def pairsFrom (lo hi : Nat) : List (Nat × Nat) :=
  (List.range' lo (hi - lo)).flatMap fun i => (List.range n127).filterMap fun j =>
    if i < j && (gmulE invsA[i]! invsA[j]! == gmulE invsA[j]! invsA[i]!) then some (i, j)
    else none

@[expose] def pairBlocks : List (Nat × Nat) :=
  [(0, 11), (11, 20), (20, 33), (33, 45), (45, 64), (64, 85), (85, 105), (105, 127)]

@[expose] def pairsL : List (Nat × Nat) := pairBlocks.flatMap fun b => pairsFrom b.1 b.2

@[expose] def memK (K : List El) (x : El) : Bool := K.any (· == x)

@[expose] def sameSet (K L : List El) : Bool := K.all (memK L) && L.all (memK K)

@[expose] def klein (a b : El) : List El := [oneE, a, b, gmulE a b]

theorem pel_length_valid : Pel.length = 1024 ∧ Pel.all validB = true := by decide +kernel

theorem invs_length : invs.length = 127 := by decide +kernel

theorem forall_pairsL {P : Nat × Nat → Prop}
    (h : ∀ k < 8, ∀ p ∈ pairsFrom (pairBlocks.getD k (0, 0)).1 (pairBlocks.getD k (0, 0)).2, P p) :
    ∀ p ∈ pairsL, P p := by
  intro p hp
  obtain ⟨b, hb, hpb⟩ := List.mem_flatMap.mp hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
  have hk8 : k < 8 := by simpa [pairBlocks] using hk
  have h2 : pairBlocks.getD k (0, 0) = pairBlocks[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  have := h k hk8 p
  rw [h2] at this
  exact this hpb

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
