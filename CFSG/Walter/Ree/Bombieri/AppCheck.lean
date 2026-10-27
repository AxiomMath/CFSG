module

public import CFSG.Walter.Ree.Bombieri.F3Poly

public section

namespace CFSG.Walter.Ree.Bombieri

namespace F3P

@[expose] def natModInv (x m : ℕ) : ℕ :=
  let rec go : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ
    | 0, _, _, s₀, _ => s₀
    | fuel + 1, r₀, r₁, s₀, s₁ =>
      if r₁ = 0 then s₀ else go fuel r₁ (r₀ % r₁) s₁ (s₀ - (r₀ / r₁) * s₁)
  ((go (2 * Nat.log2 m + 4) x m 1 0) % m).toNat

@[expose] def deg (a : F3P) : ℕ := bits (a.p ||| a.n) - 1

@[expose] def isZero (a : F3P) : Bool := a.p == 0 && a.n == 0

@[expose] def shiftX (a : F3P) (j : ℕ) : F3P := ⟨a.p <<< j, a.n <<< j⟩

@[expose] def divModAux (b : F3P) (db : ℕ) (bpos : Bool) : ℕ → F3P → F3P → F3P × F3P
  | 0, r, q => (r, q)
  | fuel + 1, r, q =>
    if isZero r then (r, q) else
    let dr := deg r
    if dr < db then (r, q) else
    let same := r.p.testBit dr == bpos
    let t := shiftX b (dr - db)
    let m := shiftX one (dr - db)
    if same then divModAux b db bpos fuel (sub r t) (add q m)
    else divModAux b db bpos fuel (add r t) (sub q m)

@[expose] def invMod (f : F3P) (k : ℕ) (a : F3P) : F3P :=
  let rec go : ℕ → F3P → F3P → F3P → F3P → F3P
    | 0, _, _, s₀, _ => s₀
    | fuel + 1, r₀, r₁, s₀, s₁ =>
      if isZero r₁ then (if r₀.p.testBit 0 then s₀ else neg s₀) else
      let db := deg r₁
      let (r, q) := divModAux r₁ db (r₁.p.testBit db) (2 * k + 4) r₀ zero
      go fuel r₁ r s₁ (sub s₀ (mulMod f k q s₁))
  go (2 * k + 4) f a zero one

@[expose] def normalize (a : F3P) : F3P := ⟨a.p, a.n ^^^ (a.n &&& a.p)⟩

@[expose] def unitCheck (f : F3P) (k : ℕ) (a : F3P) : Bool :=
  mulMod f k a (normalize (invMod f k a)) == one

@[expose] def rootCheck (f : F3P) (k : ℕ) : Bool :=
  f.p &&& f.n == 0 && f.p.testBit k && 1 ≤ k && powMod f k X (3 ^ k) == X

@[expose] def expS (k b : ℕ) : ℕ := natModInv (3 ^ b + 2) (3 ^ k - 1)

@[expose] def expA (k b : ℕ) : ℕ :=
  let h := (3 ^ k - 1) / 2
  let a₀ := natModInv ((3 ^ b + 1) / 2) h
  if a₀ % 2 = 0 then a₀ else a₀ + h

structure CaseVals where
  z : F3P
  y : F3P
  u : F3P
  A : F3P
  B : F3P
  C : F3P
  T : F3P

@[expose] def caseVals (f : F3P) (k b : ℕ) : CaseVals :=
  let s := expS k b
  let a := expA k b
  let z := powMod f k (add X one) s
  let y := powMod f k (sub X one) s
  let u := sub (powMod f k z (3 ^ b + 1)) (powMod f k y (3 ^ b + 1))
  let A := powMod f k (sub u one) a
  let B := powMod f k u a
  let C := powMod f k (add u one) a
  let T := add (sub (sub (mulMod f k z A) (mulMod f k (add (sub z y) one) B)) (mulMod f k y C))
    (mulMod f k A C)
  ⟨z, y, u, A, B, C, T⟩

@[expose] def arithCheck (k b : ℕ) : Bool :=
  let q := 3 ^ k
  let h := (q - 1) / 2
  (3 ^ b + 2) * expS k b % (q - 1) == 1 && (3 ^ b + 1) * expA k b % (q - 1) == 2 &&
    expA k b % 2 == 0 && (q - 1) % 2 == 0 && h % 2 == 1 && (3 ^ b + 1) % 2 == 0 &&
    Nat.gcd ((3 ^ b + 1) / 2) h == 1

@[expose] def checkCase (f : F3P) (k b : ℕ) : Bool :=
  let v := caseVals f k b
  arithCheck k b && unitCheck f k v.u && unitCheck f k (sub v.u one) &&
    unitCheck f k (add v.u one) && unitCheck f k v.T

@[expose] def checkK (f : F3P) (k : ℕ) : Bool :=
  rootCheck f k && (List.range k).all fun b =>
    Nat.gcd b k != 1 || 2 * b % k == 1 || Nat.gcd (3 ^ b + 2) (3 ^ k - 1) != 1 || checkCase f k b

end F3P

end CFSG.Walter.Ree.Bombieri
