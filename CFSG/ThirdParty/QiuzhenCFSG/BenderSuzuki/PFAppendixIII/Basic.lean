module

public import Mathlib.FieldTheory.Finite.GaloisField

namespace CFSG
end CFSG
open CFSG

/-!
# Appendix III Suzuki two-group interfaces
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixIII

section BasicGroup

/-- Local instance for the prime `2`, shared by Suzuki two-group coordinates and matrix models. -/
public instance instFactNatPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The finite field of order `2^m`, constructed over `ZMod 2`. -/
public abbrev BinaryGaloisField (m : ℕ) : Type :=
  GaloisField 2 m

/-- An involution is a nonidentity element whose square is one. -/
@[expose] public def IsInvolution {G : Type*} [Group G] (x : G) : Prop :=
  x ≠ 1 ∧ x ^ 2 = 1

public theorem IsInvolution.ne_one {G : Type*} [Group G] {x : G} (hx : IsInvolution x) : x ≠ 1 :=
  hx.1

/-- A strongly real element is a product of two involutions. -/
@[expose] public def IsStronglyReal {G : Type*} [Group G] (x : G) : Prop :=
  ∃ u v : G, IsInvolution u ∧ IsInvolution v ∧ x = u * v

public theorem IsInvolution.sq_eq_one {G : Type*} [Group G] {x : G} (hx : IsInvolution x) : x ^ 2 = 1 :=
  hx.2

public theorem IsInvolution.inv_eq_self {G : Type*} [Group G] {x : G} (hx : IsInvolution x) :
    x⁻¹ = x := by
  have hxx : x * x = 1 := by
    simpa [pow_two] using hx.sq_eq_one
  calc
    x⁻¹ = x⁻¹ * 1 := by simp
    _ = x⁻¹ * (x * x) := by rw [hxx]
    _ = x := by simp

/-- The set of involutions of a group. -/
@[expose] public def involutions (G : Type*) [Group G] : Set G :=
  {x : G | IsInvolution x}

/-- The right-conjugate of an element, matching the Peterfalvi convention `x^g = g⁻¹ x g`. -/
@[expose] public def rightConjugateElem {G : Type*} [Group G] (x g : G) : G :=
  g⁻¹ * x * g

public theorem isInvolution_rightConjugateElem {G : Type*} [Group G] {x g : G} (hx : IsInvolution x) :
    IsInvolution (rightConjugateElem x g) := by
  constructor
  · intro h
    apply hx.ne_one
    calc
      x = g * rightConjugateElem x g * g⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = 1 := by simp [h]
  · calc
      (rightConjugateElem x g) ^ 2 = g⁻¹ * (x ^ 2) * g := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = 1 := by simp [hx.sq_eq_one]

public theorem rightConjugateElem_rightConjugateElem {G : Type*} [Group G] {a t : G}
    (htinv : t⁻¹ = t) :
    rightConjugateElem (rightConjugateElem a t) t = a := by
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  calc
    rightConjugateElem (rightConjugateElem a t) t = t * t * a * t * t := by
      rw [rightConjugateElem, rightConjugateElem, htinv]
      group
    _ = a := by
      rw [ht2]
      simp only [one_mul]
      rw [mul_assoc, ht2, mul_one]

public theorem rightConjugateElem_involutive_of_isInvolution {G : Type*} [Group G] {t : G}
    (ht : IsInvolution t) :
    Function.Involutive (fun x : G => rightConjugateElem x t) := by
  intro x
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  calc
    rightConjugateElem (rightConjugateElem x t) t = t * (t * x) := by
      simp [rightConjugateElem, htinv, htt, mul_assoc]
    _ = (t * t) * x := by rw [mul_assoc]
    _ = x := by simp [htt]

end BasicGroup

/-- Right-conjugation by `A` is regular on the Peterfalvi set `X`. -/
@[expose]
public def ConjugationRegularOn
    {G : Type*} [Group G] (A : Subgroup G) (X : Set G) : Prop :=
  (∀ x : G, x ∈ X → ∀ a : G, a ∈ A → rightConjugateElem x a ∈ X) ∧
    ∀ x : G, x ∈ X → ∀ y : G, y ∈ X →
      ∃! a : G, a ∈ A ∧ y = rightConjugateElem x a

universe u v

/-- A group action is regular on a specified set if it preserves the set and has a unique
actor carrying any chosen point of the set to any other. -/
@[expose] public def ActionRegularOn
    (K : Type u) (P : Type v) [Group K] [Group P] [MulAction K P] (X : Set P) : Prop :=
  (∀ x : P, x ∈ X → ∀ k : K, k • x ∈ X) ∧
    ∀ x : P, x ∈ X → ∀ y : P, y ∈ X → ∃! k : K, y = k • x

/--
A Suzuki `2`-group is a `2`-group `P` such that `P` is nonabelian, `P` has at
least two involutions, and a cyclic group acts faithfully on `P` and regularly
on the set of involutions of `P`.
-/
@[expose] public def IsSuzukiTwoGroup (P : Type u) [Group P] : Prop :=
  (∃ n : ℕ, Nat.card (⊤ : Subgroup P) = 2 ^ n) ∧
  ¬ IsMulCommutative P ∧
  (∃ x y : P, IsInvolution x ∧ IsInvolution y ∧ x ≠ y) ∧
  ∃ (K : Type u) (_ : Group K) (_ : MulDistribMulAction K P),
    IsCyclic K ∧ FaithfulSMul K P ∧ ActionRegularOn K P (involutions P)
/-!
# Appendix III Suzuki two-group coordinate interfaces
-/
/-- PF Appendix III, Definition 2: a Suzuki `2`-group of type A. -/
@[expose] public def IsSuzukiTwoTypeA {G : Type u} [Group G] (S : Subgroup G) : Prop :=
  ∃ (n : ℕ) (_ : n ≠ 0)
      (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (pairLift : BinaryGaloisField n → BinaryGaloisField n → G)
      (cocycle : BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n),
    (∃ r : ℕ, Odd r ∧ 0 < r ∧
      ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
    (∃ x : BinaryGaloisField n, theta x ≠ x) ∧
    (∀ a b c : BinaryGaloisField n,
      cocycle (a + b) c = cocycle a c + cocycle b c) ∧
    (∀ a b c : BinaryGaloisField n,
      cocycle a (b + c) = cocycle a b + cocycle a c) ∧
    (∀ a : BinaryGaloisField n, cocycle a a = a * theta a) ∧
    (∀ a z : BinaryGaloisField n, pairLift a z ∈ S) ∧
    pairLift 0 0 = 1 ∧
    (∀ x : G, x ∈ S → ∃ a z : BinaryGaloisField n, x = pairLift a z) ∧
    (∀ a z b w : BinaryGaloisField n,
      pairLift a z = pairLift b w → a = b ∧ z = w) ∧
    (∀ a z b w : BinaryGaloisField n,
      pairLift a z * pairLift b w =
        pairLift (a + b) (z + w + cocycle a b))

/-- PF Appendix III, Definition 3: a Suzuki `2`-group of type B. -/
@[expose] public def IsSuzukiTwoTypeB {G : Type u} [Group G] (S : Subgroup G) : Prop :=
  ∃ (n : ℕ) (_ : n ≠ 0)
      (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (epsilon : BinaryGaloisField n)
      (tripleLift :
        BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n → G)
      (cocycle :
        BinaryGaloisField n → BinaryGaloisField n →
          BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n),
    epsilon ≠ 0 ∧
    (∃ r : ℕ, Odd r ∧ 0 < r ∧
      ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
    (∀ a b : BinaryGaloisField n, a ≠ 0 → b ≠ 0 →
      a * theta a + epsilon * a * theta b + b * theta b ≠ 0) ∧
    (∀ a b e f c d : BinaryGaloisField n,
      cocycle (a + e) (b + f) c d = cocycle a b c d + cocycle e f c d) ∧
    (∀ a b e f c d : BinaryGaloisField n,
      cocycle a b (e + c) (f + d) = cocycle a b e f + cocycle a b c d) ∧
    (∀ a b : BinaryGaloisField n,
      cocycle a b a b = a * theta a + epsilon * a * theta b + b * theta b) ∧
    (∀ c a b : BinaryGaloisField n, tripleLift c a b ∈ S) ∧
    tripleLift 0 0 0 = 1 ∧
    (∀ x : G, x ∈ S → ∃ c a b : BinaryGaloisField n, x = tripleLift c a b) ∧
    (∀ c a b d e f : BinaryGaloisField n,
      tripleLift c a b = tripleLift d e f → c = d ∧ a = e ∧ b = f) ∧
    (∀ c a b d e f : BinaryGaloisField n,
      tripleLift c a b * tripleLift d e f =
        tripleLift (c + d + cocycle a b e f) (a + e) (b + f))

/-- In a type-B Suzuki two-group, every involution is central. -/
public theorem IsSuzukiTwoTypeB.commute_of_isInvolution
    {G : Type u} [Group G] {S : Subgroup G} (hB : IsSuzukiTwoTypeB S)
    {x y : G} (hxS : x ∈ S) (hxI : IsInvolution x) (hyS : y ∈ S) :
    Commute x y := by
  rcases hB with ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
    hperiod, hnonzero, haddLeft, haddRight, hdiag, hmem, hone,
    hsurj, hinj, hmul⟩
  rcases hsurj x hxS with ⟨c, a, b, rfl⟩
  rcases hsurj y hyS with ⟨d, e, f, rfl⟩
  have hsquare :
      tripleLift c a b * tripleLift c a b = tripleLift 0 0 0 := by
    rw [← pow_two, hxI.sq_eq_one, hone]
  have hsquare' :
      tripleLift (c + c + cocycle a b a b) (a + a) (b + b) =
        tripleLift 0 0 0 := by
    rw [← hmul]
    exact hsquare
  have hcoords := hinj _ _ _ 0 0 0 hsquare'
  have hcocycle : cocycle a b a b = 0 := by
    have h := hcoords.1
    rw [CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  have hquad : a * theta a + epsilon * a * theta b + b * theta b = 0 := by
    rw [← hdiag]
    exact hcocycle
  have hab : a = 0 ∧ b = 0 := by
    by_cases ha : a = 0
    · subst a
      simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add] at hquad
      rcases mul_eq_zero.mp hquad with hb | htb
      · exact ⟨rfl, hb⟩
      · exact ⟨rfl, theta.injective (by simpa using htb)⟩
    · by_cases hb : b = 0
      · subst b
        simp only [map_zero, mul_zero, add_zero] at hquad
        rcases mul_eq_zero.mp hquad with ha' | hta
        · exact ⟨ha', rfl⟩
        · exact ⟨theta.injective (by simpa using hta), rfl⟩
      · exact False.elim (hnonzero a b ha hb hquad)
  rcases hab with ⟨rfl, rfl⟩
  have hzeroLeft : cocycle 0 0 e f = 0 := by
    have hzero := haddLeft 0 0 0 0 e f
    simpa using hzero
  have hzeroRight : cocycle e f 0 0 = 0 := by
    have hzero := haddRight e f 0 0 0 0
    simpa using hzero
  change tripleLift c 0 0 * tripleLift d e f =
    tripleLift d e f * tripleLift c 0 0
  rw [hmul, hmul, hzeroLeft, hzeroRight]
  simp [add_comm]

end PFAppendixIII
end CFSG.BenderSuzuki
