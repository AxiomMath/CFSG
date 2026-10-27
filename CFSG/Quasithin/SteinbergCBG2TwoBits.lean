module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.SteinbergCB.G2Two

abbrev F2 : Type := ZMod 2

@[expose] def toV (n : ℕ) (x : ℕ) : Fin n → F2 := fun i => if x.testBit i then 1 else 0

theorem toV_xor (n x y : ℕ) : toV n (x ^^^ y) = toV n x + toV n y := by
  funext i
  simp only [toV, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem toV_zero (n : ℕ) : toV n 0 = 0 := by
  funext i
  simp [toV]

theorem toV_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : toV n x = toV n y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrFun h ⟨i, hi⟩
    simp only [toV] at this
    cases hxi : x.testBit i <;> cases hyi : y.testBit i <;> simp_all
  · push Not at hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hi))]

@[expose] def ofV {n : ℕ} (v : Fin n → F2) : ℕ := ∑ i : Fin n, (v i).val * 2 ^ (i : ℕ)

theorem ofV_lt {n : ℕ} (v : Fin n → F2) : ofV v < 2 ^ n := by
  unfold ofV
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i => v i.castSucc)
    have h2 : (v (Fin.last n)).val ≤ 1 := Nat.lt_succ_iff.1 (ZMod.val_lt (v (Fin.last n)))
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    calc ∑ i : Fin n, (v i.castSucc).val * 2 ^ (i : ℕ) + (v (Fin.last n)).val * 2 ^ n
        < 2 ^ n + 1 * 2 ^ n := by
          apply Nat.add_lt_add_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
      _ = 2 ^ (n + 1) := by ring

theorem testBit_ofV {n : ℕ} (v : Fin n → F2) (i : Fin n) :
    (ofV v).testBit i = decide (v i = 1) := by
  unfold ofV
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hlt := ofV_lt (fun j : Fin n => v j.castSucc)
    unfold ofV at hlt
    have hv : (v (Fin.last n)).val = 0 ∨ (v (Fin.last n)).val = 1 := by
      have := ZMod.val_lt (v (Fin.last n)); omega
    have key : ∑ j : Fin n, (v j.castSucc).val * 2 ^ (j.castSucc : ℕ) +
        (v (Fin.last n)).val * 2 ^ (Fin.last n : ℕ) =
        2 ^ n * (v (Fin.last n)).val + ∑ j : Fin n, (v j.castSucc).val * 2 ^ (j : ℕ) := by
      simp only [Fin.val_castSucc, Fin.val_last]
      ring
    rw [key, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hi : (i : ℕ) < n
    · simp only [hi, ↓reduceIte]
      have := ih (fun j => v j.castSucc) ⟨i, hi⟩
      simp only at this
      rw [this]
      congr 2
    · have hi' : i = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
      simp only [hi, ↓reduceIte]
      rw [hi']
      simp only [Fin.val_last, Nat.sub_self]
      rcases hv with hv | hv
      · rw [hv]
        have : v (Fin.last n) = 0 := (ZMod.val_eq_zero _).1 hv
        simp [this]
      · rw [hv]
        have : v (Fin.last n) = 1 := by
          rw [← ZMod.natCast_zmod_val (v (Fin.last n)), hv, Nat.cast_one]
        simp [this]

theorem toV_ofV {n : ℕ} (v : Fin n → F2) : toV n (ofV v) = v := by
  funext i
  simp only [toV, testBit_ofV]
  have : v i = 0 ∨ v i = 1 := by
    rcases (show (v i).val = 0 ∨ (v i).val = 1 by have := ZMod.val_lt (v i); omega) with h | h
    · exact Or.inl ((ZMod.val_eq_zero _).1 h)
    · right
      rw [← ZMod.natCast_zmod_val (v i), h, Nat.cast_one]
  rcases this with h | h <;> simp [h]

theorem toV_surj {n : ℕ} (v : Fin n → F2) : ∃ x < 2 ^ n, toV n x = v :=
  ⟨ofV v, ofV_lt v, toV_ofV v⟩

theorem eq_of_toV {n : ℕ} {X : Type*} {f g : (Fin n → F2) → X}
    (h : ∀ x < 2 ^ n, f (toV n x) = g (toV n x)) : f = g := by
  funext v
  obtain ⟨x, hx, rfl⟩ := toV_surj v
  exact h x hx

@[expose] def mApp : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, x => (if x % 2 = 1 then c else 0) ^^^ mApp cs (x / 2)

theorem mApp_zero : ∀ M : List ℕ, mApp M 0 = 0
  | [] => rfl
  | c :: cs => by simp [mApp, mApp_zero cs]

theorem mApp_xor : ∀ (M : List ℕ) (x y : ℕ), mApp M (x ^^^ y) = mApp M x ^^^ mApp M y
  | [], _, _ => by simp [mApp]
  | c :: cs, x, y => by
    simp only [mApp, Nat.xor_div_two, mApp_xor cs]
    have hx : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    have hy : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
    have hxy : (x ^^^ y) % 2 = (x + y) % 2 := Nat.xor_mod_two_eq
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have : (x ^^^ y) % 2 = 0 := by omega
      simp [hx, hy, this]
    · have : (x ^^^ y) % 2 = 1 := by omega
      simp only [hx, hy, this, ↓reduceIte, zero_ne_one, Nat.zero_xor]
      ac_rfl
    · have : (x ^^^ y) % 2 = 1 := by omega
      simp only [hx, hy, this, ↓reduceIte, zero_ne_one, Nat.zero_xor]
      ac_rfl
    · have : (x ^^^ y) % 2 = 0 := by omega
      simp only [hx, hy, this, ↓reduceIte, zero_ne_one, Nat.zero_xor]
      calc mApp cs (x / 2) ^^^ mApp cs (y / 2) = 0 ^^^ (mApp cs (x / 2) ^^^ mApp cs (y / 2)) :=
            (Nat.zero_xor _).symm
        _ = (c ^^^ c) ^^^ (mApp cs (x / 2) ^^^ mApp cs (y / 2)) := by rw [Nat.xor_self]
        _ = c ^^^ mApp cs (x / 2) ^^^ (c ^^^ mApp cs (y / 2)) := by ac_rfl

@[expose] def mComp (M N : List ℕ) : List ℕ := N.map (mApp M)

theorem mApp_mComp (M : List ℕ) : ∀ (N : List ℕ) (x : ℕ),
    mApp (mComp M N) x = mApp M (mApp N x)
  | [], _ => by simp [mComp, mApp, mApp_zero]
  | n :: ns, x => by
    have ih := mApp_mComp M ns (x / 2)
    simp only [mComp, List.map_cons, mApp] at ih ⊢
    rw [ih, mApp_xor]
    congr 1
    split_ifs <;> simp [mApp_zero]

@[expose] def certOK (n : ℕ) (gens : List (List ℕ)) : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | seen, (y, k, x) :: rest =>
    seen.contains x && decide (k < gens.length) && decide (y < 2 ^ n) &&
      mApp (gens.getD k []) x == y && certOK n gens (y :: seen) rest

theorem mem_orbit_of_certOK {H X : Type*} [Group H] [MulAction H X] (n : ℕ) (pt : ℕ → X)
    (gens : List (List ℕ))
    (hgens : ∀ k < gens.length, ∃ h : H, ∀ x < 2 ^ n, h • pt x = pt (mApp (gens.getD k []) x))
    (base : X) : ∀ (cert : List (ℕ × ℕ × ℕ)) (seen : List ℕ),
      (∀ s ∈ seen, s < 2 ^ n ∧ pt s ∈ MulAction.orbit H base) →
      certOK n gens seen cert = true → ∀ t ∈ cert, t.1 < 2 ^ n ∧ pt t.1 ∈ MulAction.orbit H base
  | [], _, _, _ => by simp
  | (y, k, x) :: rest, seen, hseen, hc => by
    simp only [certOK, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨hx, hk⟩, hy⟩, hyx⟩, hrest⟩ := hc
    obtain ⟨h, hh⟩ := hgens k hk
    obtain ⟨hxlt, hxo⟩ := hseen x hx
    have hyo : pt y ∈ MulAction.orbit H base := by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hxo
      refine MulAction.mem_orbit_iff.2 ⟨h * g, ?_⟩
      rw [mul_smul, hg, hh x hxlt, hyx]
    have hseen' : ∀ s ∈ y :: seen, s < 2 ^ n ∧ pt s ∈ MulAction.orbit H base := by
      intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact ⟨hy, hyo⟩
      · exact hseen s hs
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨hy, hyo⟩
    · exact mem_orbit_of_certOK n pt gens hgens base rest (y :: seen) hseen' hrest t ht

end CFSG.Quasithin.SteinbergCB.G2Two
