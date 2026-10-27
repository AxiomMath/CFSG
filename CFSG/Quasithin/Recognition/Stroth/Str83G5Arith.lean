module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Quasithin.Stroth.G5

abbrev Coord (n : ℕ) : Type := ZMod (2 ^ n - 1) × ZMod (2 ^ n - 1)

variable {n : ℕ}

@[expose] def psi (m₀ : ZMod (2 ^ n - 1)) : Coord n := (1, m₀)

@[expose] def chi (k₀ : ZMod (2 ^ n - 1)) : Coord n := (k₀, 1)

@[expose] def sigma1 (m₀ : ZMod (2 ^ n - 1)) (φ : Coord n) : Coord n := (-φ.1, φ.2 - 2 * m₀ * φ.1)

@[expose] def sigma2 (k₀ : ZMod (2 ^ n - 1)) (φ : Coord n) : Coord n := (φ.1 - 2 * k₀ * φ.2, -φ.2)

@[expose] def mPow (k₀ m₀ : ZMod (2 ^ n - 1)) : ℤ → Coord n → Coord n
  | (t : ℕ) => (sigma2 k₀ ∘ sigma1 m₀)^[t]
  | Int.negSucc t => (sigma1 m₀ ∘ sigma2 k₀)^[t + 1]

@[expose] def cen (n : ℕ) : ZMod (2 ^ n - 1) := 1 + 2 ^ ((n + 1) / 2)

@[expose] def cls (φ : Coord n) : Finset (Coord n) :=
  (Finset.range n).image fun s => ((2 : ZMod (2 ^ n - 1)) ^ s) • φ

structure Pattern where
  s2 : ℕ
  s1 : ℕ
  l1 : ℕ
deriving DecidableEq

namespace Pattern

@[expose] def target : Pattern := ⟨7, 7, 7⟩

@[expose] def dS (p : Pattern) (m : ℕ) : ℕ := if m ≤ p.s2 then 2 else if m ≤ p.s1 then 1 else 0

@[expose] def dL (p : Pattern) (m : ℕ) : ℕ := if m ≤ p.l1 then 1 else 0

@[expose] def eS (p : Pattern) (m : ℕ) : ℤ :=
  10 - ∑ j ∈ Finset.Ico 1 m, (if Even j then (p.dS j : ℤ) else p.dL j)

@[expose] def oS (p : Pattern) (m : ℕ) : ℤ :=
  11 - ∑ j ∈ Finset.Ico 1 m, (if Even j then (p.dL j : ℤ) else p.dS j)

@[expose] def Admissible (p : Pattern) : Prop :=
  1 ≤ p.s2 ∧ p.s2 ≤ p.s1 ∧ 1 ≤ p.l1 ∧ (∀ m, 1 ≤ m → 0 ≤ p.eS m) ∧ (∀ m, 1 ≤ m → 0 ≤ p.oS m) ∧
    ∀ m, 1 ≤ m → Even m → p.eS m = p.oS m

@[expose] def J (p : Pattern) : ℕ := max p.s1 p.l1

@[expose] def ell (p : Pattern) : ℕ := (p.eS (p.J + 1)).toNat

@[expose] def dropAt (p : Pattern) (l : ℤ) (m : ℕ) : ℕ := if Even l then p.dS m else p.dL m

@[expose] def contrib (k₀ m₀ : ZMod (2 ^ n - 1)) (s : ZMod (2 ^ n - 1)) (l : ℤ) (d : ℕ) :
    Multiset (Coord n) :=
  if Even l then
    if d = 2 then {s • mPow k₀ m₀ (l / 2) (psi m₀), cen n • s • mPow k₀ m₀ (l / 2) (psi m₀)}
    else if d = 1 then {cen n • s • mPow k₀ m₀ (l / 2) (psi m₀)} else 0
  else if d = 1 then {s • mPow k₀ m₀ ((l - 1) / 2) (chi k₀)} else 0

@[expose] def chainR (p : Pattern) (k₀ m₀ : ZMod (2 ^ n - 1)) (i j : ℤ) : Multiset (Coord n) :=
  ∑ l ∈ Finset.Ioc j (i + p.J), contrib k₀ m₀ 1 l (p.dropAt l (l - i).toNat)

@[expose] def chainL (p : Pattern) (k₀ m₀ : ZMod (2 ^ n - 1)) (i j : ℤ) : Multiset (Coord n) :=
  ∑ l ∈ Finset.Ico (j - p.J) i, contrib k₀ m₀ (-1) l (p.dropAt l (j - l).toNat)

@[expose] def Pass (p : Pattern) (k₀ m₀ : ZMod (2 ^ n - 1)) (i j : ℤ) : Prop :=
  (p.chainR k₀ m₀ i j).map cls = (p.chainL k₀ m₀ i j).map cls

end Pattern

@[expose] def Str83G5ArithGoal : Prop :=
  ∀ (n : ℕ), Odd n → 3 ≤ n → ∀ k₀ m₀ : ZMod (2 ^ n - 1), IsUnit k₀ → IsUnit m₀ →
    ∀ p : Pattern, p.Admissible → (∀ i j : ℤ, i ≤ j → j ≤ i + p.J → p.Pass k₀ m₀ i j) →
      ∀ μT : Multiset (Coord n),
        (μT.map (sigma1 m₀)).map cls = μT.map cls →
        (μT.map (sigma2 k₀)).map cls = μT.map cls →
        (μT.map fun φ => (cls φ).card).sum = n * p.ell →
        (∀ φ ∈ p.chainR k₀ m₀ 0 0 + μT, φ.1 = 0 ∨ IsUnit φ.1) →
        4 ∣ ((p.chainR k₀ m₀ 0 0 + μT).filter fun φ => φ.1 ≠ 0).card →
        4 ∣ ((p.chainR k₀ m₀ 0 0 + μT).filter fun φ => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1).card →
        p = Pattern.target

end CFSG.Quasithin.Stroth.G5

end
