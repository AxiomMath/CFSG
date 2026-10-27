module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Arith
public import Mathlib.Algebra.Ring.Int.Parity

public section

namespace CFSG.Quasithin.Stroth.G5

structure Lab where
  isPsi : Bool
  t : ℤ
  neg : Bool
  ctr : Bool
deriving DecidableEq, Repr

variable {n : ℕ}

@[expose] def sgn (b : Bool) : ZMod (2 ^ n - 1) := if b then -1 else 1

@[expose] def Lab.val (k₀ m₀ : ZMod (2 ^ n - 1)) (l : Lab) : Coord n :=
  (sgn (n := n) l.neg) • if l.isPsi then
    (if l.ctr then G5.cen n else 1) • mPow k₀ m₀ l.t (psi m₀) else mPow k₀ m₀ l.t (chi k₀)

@[expose] def labContrib (s : Bool) (l : ℤ) (d : ℕ) : Multiset Lab :=
  if Even l then
    if d = 2 then {⟨true, l / 2, s, false⟩, ⟨true, l / 2, s, true⟩}
    else if d = 1 then {⟨true, l / 2, s, true⟩} else 0
  else if d = 1 then {⟨false, (l - 1) / 2, s, false⟩} else 0

namespace Pattern

@[expose] def labR (p : Pattern) (i j : ℤ) : Multiset Lab :=
  ∑ l ∈ Finset.Ioc j (i + p.J), labContrib false l (p.dropAt l (l - i).toNat)

@[expose] def labL (p : Pattern) (i j : ℤ) : Multiset Lab :=
  ∑ l ∈ Finset.Ico (j - p.J) i, labContrib true l (p.dropAt l (j - l).toNat)

@[expose] def windowLabs (p : Pattern) : List (Multiset Lab × Multiset Lab) :=
  [(0 : ℤ), 1].flatMap fun i => (List.range (p.J + 1)).map fun d =>
    (p.labR i (i + d), p.labL i (i + d))

@[expose] def admissibleB (p : Pattern) : Bool :=
  decide (1 ≤ p.s2) && decide (p.s2 ≤ p.s1) && decide (1 ≤ p.l1) &&
    (List.range (p.J + 3)).all fun m =>
      m == 0 || (decide (0 ≤ p.eS m) && decide (0 ≤ p.oS m) &&
        (!decide (Even m) || decide (p.eS m = p.oS m)))

@[expose] def p16 : Pattern := ⟨3, 3, 3⟩

@[expose] def p17 : Pattern := ⟨3, 3, 11⟩

@[expose] def p18 : Pattern := ⟨3, 11, 3⟩

@[expose] def p20 : Pattern := ⟨5, 5, 5⟩

@[expose] def p73 : Pattern := ⟨7, 7, 3⟩

end Pattern

@[expose] def admissibleList (_ : Unit := ()) : List Pattern :=
  ((List.range 25).flatMap fun s1 => (List.range (s1 + 1)).flatMap fun s2 =>
    (List.range 25).map fun l1 => (⟨s2, s1, l1⟩ : Pattern)).filter Pattern.admissibleB

inductive AType
  | unlinked (r : ℕ) (e : Bool) (r' : ℕ) (e' : Bool)
  | linked (r : ℕ) (ε₀ δ₀ : Bool)
deriving DecidableEq, Repr

@[expose] def redA (r : ℕ) (e : Bool) (t : ℤ) (ε : Bool) : ℤ × Bool :=
  if r = 0 then (t, ε) else (t % r, xor ε (e && decide (Odd (t / r))))

@[expose] def AType.canon : AType → Lab → Lab
  | .unlinked r e _ _, ⟨true, t, ε, δ⟩ => ⟨true, (redA r e t ε).1, (redA r e t ε).2, δ⟩
  | .unlinked _ _ r' e', ⟨false, t, ε, _⟩ => ⟨false, (redA r' e' t ε).1, (redA r' e' t ε).2, false⟩
  | .linked r _ _, ⟨true, t, ε, δ⟩ => ⟨true, t % r, ε, δ⟩
  | .linked r ε₀ δ₀, ⟨false, t, ε, _⟩ => ⟨true, (t + ((r + 1) / 2 : ℕ)) % r, xor ε ε₀, δ₀⟩

@[expose] def AType.passAll (τ : AType) (p : Pattern) : Bool :=
  p.windowLabs.all fun w => decide (w.1.map τ.canon = w.2.map τ.canon)

@[expose] def typeList (Δ : ℕ) : List AType :=
  ((List.range (Δ + 1)).flatMap fun r => (if r = 0 then [false] else [false, true]).flatMap
      fun e => (List.range (Δ + 1)).flatMap fun r' =>
        (if r' = 0 then [false] else [false, true]).map fun e' => AType.unlinked r e r' e') ++
    ((List.range (Δ + 1)).map fun k => 2 * k + 1).flatMap fun r =>
      [false, true].flatMap fun ε₀ => [false, true].map fun δ₀ => AType.linked r ε₀ δ₀

@[expose] def pairs30 : List (ℕ × ℕ) :=
  (List.range 10).map (fun k => (1, k + 1)) ++ [(2, 1), (3, 1), (4, 1), (5, 1)] ++
    ((List.range 7).map fun k => (2, k + 2)) ++ [(3, 2), (4, 2), (5, 2)] ++
    [(3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4)]

@[expose] def okType (p : Pattern) : AType → Bool
  | .unlinked r true r' true =>
      decide ((r, r') ∈ pairs30) &&
        (!decide ((r, r') = (2, 2) ∨ (r, r') = (2, 6)) ||
          decide (p = .p16 ∨ p = .p17 ∨ p = .p18)) &&
        (!decide ((r, r') = (3, 3)) || decide (p = .p20)) &&
        (!decide ((r, r') = (4, 4)) || decide (p = .target))
  | _ => false

@[expose] def typeCheck (_ : Unit := ()) : Bool :=
  (admissibleList ()).all fun p =>
    (typeList (p.J + 2)).all fun τ => !τ.passAll p || okType p τ

@[expose] def passAllConc (p : Pattern) (k₀ m₀ : ZMod (2 ^ n - 1)) : Bool :=
  [(0 : ℤ), 1].all fun i => (List.range (p.J + 1)).all fun d =>
    decide ((p.chainR k₀ m₀ i (i + d)).map cls = (p.chainL k₀ m₀ i (i + d)).map cls)

@[expose] def okThree (p : Pattern) (k₀ m₀ : ZMod (2 ^ 3 - 1)) : Bool :=
  (decide (p = .p16 ∨ p = .p17 ∨ p = .p18 ∨ p = .p73) && decide (4 * k₀ * m₀ - 2 = 0)) ||
    (decide (p = .p20) && decide (4 * k₀ * m₀ - 2 = 1)) || decide (p = .target)

@[expose] def threeCheck (_ : Unit := ()) : Bool :=
  (admissibleList ()).all fun p =>
    (List.range 6).all fun k => (List.range 6).all fun m =>
      !passAllConc (n := 3) p (k + 1 : ℕ) (m + 1 : ℕ) || okThree p (k + 1 : ℕ) (m + 1 : ℕ)

end CFSG.Quasithin.Stroth.G5

end
