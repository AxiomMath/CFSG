module

public import CFSG.Fischer.F4
public import CFSG.Sporadic.Co2Smith.GlDataRootInputs

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Fischer CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def f4c (n : Nat) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def m6Get (a : Array F4) (i j : Nat) : F4 := a.getD (6 * i + j) 0

@[expose] def m6Mul (a b : Array F4) : Array F4 := Array.ofFn fun k : Fin 36 =>
  m6Get a (k.val / 6) 0 * m6Get b 0 (k.val % 6) + m6Get a (k.val / 6) 1 * m6Get b 1 (k.val % 6) +
    m6Get a (k.val / 6) 2 * m6Get b 2 (k.val % 6) + m6Get a (k.val / 6) 3 * m6Get b 3 (k.val % 6) +
    m6Get a (k.val / 6) 4 * m6Get b 4 (k.val % 6) + m6Get a (k.val / 6) 5 * m6Get b 5 (k.val % 6)

@[expose] def m6One : Array F4 := Array.ofFn fun k : Fin 36 =>
  if k.val / 6 = k.val % 6 then 1 else 0

@[expose] def stPosI : Array Nat := #[0, 0, 0, 0, 1, 1, 5, 5, 5, 5, 4, 4, 0, 1, 2, 5, 4, 3]

@[expose] def stPosJ : Array Nat := #[4, 3, 2, 1, 3, 2, 1, 2, 3, 4, 2, 3, 5, 4, 3, 0, 1, 2]

@[expose] def stEltS (i j c : Nat) : Array F4 := Array.ofFn fun k : Fin 36 =>
  (if k.val / 6 = k.val % 6 then 1 else 0) +
    (if i = k.val / 6 ∧ j = k.val % 6 then f4c c else 0) +
    (if 5 - j = k.val / 6 ∧ 5 - i = k.val % 6 then f4c c * f4c c else 0)

@[expose] def stEltL (i j c : Nat) : Array F4 := Array.ofFn fun k : Fin 36 =>
  (if k.val / 6 = k.val % 6 then 1 else 0) +
    (if i = k.val / 6 ∧ j = k.val % 6 ∧ c % 4 ≠ 0 then 1 else 0)

@[expose] def stElt (r c : Nat) : Array F4 :=
  if r < 12 then stEltS (stPosI.getD r 0) (stPosJ.getD r 0) c
  else stEltL (stPosI.getD r 0) (stPosJ.getD r 0) c

@[expose] def stFund : Array (Int × Int × Int) :=
  #[(1, 2, 1), (1, 1, 1), (1, 1, 0), (1, 0, 0), (0, 1, 1), (0, 1, 0), (-1, -2, -1), (-1, -1, -1),
    (-1, -1, 0), (-1, 0, 0), (0, -1, -1), (0, -1, 0), (2, 2, 1), (0, 2, 1), (0, 0, 1),
    (-2, -2, -1), (0, -2, -1), (0, 0, -1)]

@[expose] def stDot (f v : Int × Int × Int) : Int := f.1 * v.1 + f.2.1 * v.2.1 + f.2.2 * v.2.2

@[expose] def stCoeffs : List Int := [-2, -1, 0, 1, 2]

@[expose] def stFL : List (Int × Int × Int) :=
  stCoeffs.flatMap fun a => stCoeffs.flatMap fun b => stCoeffs.map fun c => (a, b, c)

@[expose] def stBlock (r s : Nat) : List Nat :=
  (List.range 18).filter fun t => stFL.all fun f =>
    !(decide (0 ≤ stDot f (stFund.getD r (0, 0, 0))) &&
        decide (0 ≤ stDot f (stFund.getD s (0, 0, 0)))) ||
      decide (0 ≤ stDot f (stFund.getD t (0, 0, 0)))

@[expose] def stOpp (r s : Nat) : Bool :=
  let a := stFund.getD r (0, 0, 0)
  let b := stFund.getD s (0, 0, 0)
  a.1 == -b.1 && a.2.1 == -b.2.1 && a.2.2 == -b.2.2

@[expose] def stParams (t : Nat) : List Nat := if t < 12 then [0, 1, 2, 3] else [0, 1]

@[expose] def stGens (B : List Nat) : List (Array F4 × Array Nat) :=
  B.flatMap fun t => (stParams t).map fun c => (stElt t c, glRootRows t c)

@[expose] def stStep (gens : List (Array F4 × Array Nat)) (acc : Array (Array F4 × Array Nat))
    (p : Array F4 × Array Nat) : Array (Array F4 × Array Nat) :=
  gens.foldl (fun acc g =>
    let q := (m6Mul p.1 g.1, mulRows 22 p.2 g.2)
    if acc.any (fun e => e.1 == q.1) then acc else acc.push q) acc

@[expose] def stBFS (gens : List (Array F4 × Array Nat)) :
    Nat → Array (Array F4 × Array Nat) → Nat → Array (Array F4 × Array Nat)
  | 0, acc, _ => acc
  | fuel + 1, acc, i =>
    if i < acc.size then stBFS gens fuel (stStep gens acc (acc.getD i (m6One, idRows 22))) (i + 1)
    else acc

@[expose] def stCheck (gens : List (Array F4 × Array Nat)) : Bool :=
  let Γ := stBFS gens 200 #[(m6One, idRows 22)] 0
  let n := Γ.size
  decide (0 < n) && (Γ.getD 0 (m6One, idRows 22)).1 == m6One &&
    (Γ.getD 0 (m6One, idRows 22)).2 == idRows 22 &&
    ((List.range n).all fun i => (List.range n).all fun j =>
      i == j || !((Γ.getD i (m6One, idRows 22)).1 == (Γ.getD j (m6One, idRows 22)).1)) &&
    (List.range n).all fun i => gens.all fun g => (List.range n).any fun j =>
      (Γ.getD j (m6One, idRows 22)).1 == m6Mul (Γ.getD i (m6One, idRows 22)).1 g.1 &&
        (Γ.getD j (m6One, idRows 22)).2 == mulRows 22 (Γ.getD i (m6One, idRows 22)).2 g.2

@[expose] def glSteinOK : Bool :=
  ((List.range 18).all fun r => (List.range 18).all fun s =>
    stOpp r s || stCheck (stGens (stBlock r s))) &&
  [[3, 9], [5, 11], [14, 17]].all fun B => stCheck (stGens B)

end CFSG.Sporadic.Co2Smith.Native
