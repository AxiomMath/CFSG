module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7Defs
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6 CFSG.Permutation.FinPack

namespace M7

set_option maxRecDepth 100000

@[expose] def bitsOf (f : ℕ → Bool) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (bif f i then 1 <<< i else 0)) m

theorem testBit_bitsOf (f : ℕ → Bool) : ∀ (m j : ℕ),
    (bitsOf f m).testBit j = (decide (j < m) && f j)
  | 0, j => by simp [bitsOf]
  | m + 1, j => by
    change (bitsOf f m ||| (bif f m then 1 <<< m else 0)).testBit j = _
    rw [Nat.testBit_or, testBit_bitsOf f m j]
    by_cases hj : j = m
    · subst hj
      cases f j <;> simp [Nat.one_shiftLeft]
    · have e : (bif f m then 1 <<< m else 0).testBit j = false := by
        cases f m <;> simp [Nat.one_shiftLeft, Ne.symm hj]
      rw [e, Bool.or_false]
      by_cases h : j < m
      · simp [h, show j < m + 1 by omega]
      · simp [h, show ¬ j < m + 1 by omega]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

@[expose] def decP (c : ℕ) : PermMod 7 :=
  Multiplicative.ofAdd fun i => if c.testBit i then 1 else 0

@[expose] def encP (z : PermMod 7) : ℕ :=
  bitsOf (fun i => if h : i < 7 then decide (Multiplicative.toAdd z ⟨i, h⟩ = 1) else false) 7

theorem testBit_encP (z : PermMod 7) (j : ℕ) :
    (encP z).testBit j = if h : j < 7 then decide (Multiplicative.toAdd z ⟨j, h⟩ = 1) else false := by
  rw [encP, testBit_bitsOf]
  by_cases h : j < 7 <;> simp [h]

theorem decP_encP (z : PermMod 7) : decP (encP z) = z := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [decP, toAdd_ofAdd, testBit_encP, i.isLt, dite_true]
  rcases zmod2_cases (Multiplicative.toAdd z i) with h | h <;> simp [h]

theorem encP_lt (z : PermMod 7) : encP z < 128 := by
  have : encP z < 2 ^ 7 := Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [testBit_encP, dif_neg (by omega)]
  simpa using this

theorem encP_injective : Function.Injective encP := fun x y h => by
  rw [← decP_encP x, ← decP_encP y, h]

theorem encP_mul (x y : PermMod 7) : encP (x * y) = encP x ^^^ encP y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_encP, testBit_encP, testBit_encP]
  by_cases h : j < 7
  · simp only [h, dite_true, toAdd_mul, Pi.add_apply]
    rcases zmod2_cases (Multiplicative.toAdd x ⟨j, h⟩) with hx | hx <;>
      rcases zmod2_cases (Multiplicative.toAdd y ⟨j, h⟩) with hy | hy <;> simp [hx, hy] <;> decide
  · simp [h]

theorem encP_one : encP 1 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_encP, Nat.zero_testBit]
  split <;> simp

@[expose] def permK (s : Perm (Fin 7)) (c : ℕ) : ℕ :=
  bitsOf (fun i => if h : i < 7 then c.testBit (s⁻¹ ⟨i, h⟩) else false) 7

theorem encP_permAct (s : Perm (Fin 7)) (z : PermMod 7) : encP (permAct 7 s z) = permK s (encP z) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [permK, testBit_bitsOf, testBit_encP]
  by_cases h : j < 7
  · simp only [h, dite_true, decide_true, Bool.true_and, permAct_apply, testBit_encP,
      (s⁻¹ ⟨j, h⟩).isLt]
    rfl
  · simp [h]

@[expose] def condZK (c : ℕ) : Bool :=
  decide (∑ i, Multiplicative.toAdd (decP c) i = 0) && !Nat.beq c 0 &&
    gens.all fun s => Nat.beq (permK s c) c

@[expose] def condVK (c d : ℕ) : Bool :=
  decide (∑ i, Multiplicative.toAdd (decP d) i = 0) && !Nat.beq d 0 && !Nat.beq d c &&
    (gens.all fun s => Nat.beq (permK s d) d || Nat.beq (permK s d) (c ^^^ d)) &&
    (decide (wt (decP d) = wt (decP c)) || decide (wt (decP (c ^^^ d)) = wt (decP c)))

@[expose] def conclK (c d : ℕ) : Bool :=
  (Nat.beq c (encP a) && (Nat.beq d (encP w) || Nat.beq d (encP a ^^^ encP w))) ||
    (Nat.beq c (encP b) && (Nat.beq d (encP t1) || Nat.beq d (encP t2)))

theorem beq_encP (x y : PermMod 7) : Nat.beq (encP x) (encP y) = decide (x = y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  exact ⟨fun h => encP_injective h, fun h => h ▸ rfl⟩

theorem condZK_of {z : PermMod 7} (h : CondZ z) : condZK (encP z) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [condZK, decP_encP, h1, decide_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true]
  refine ⟨?_, fun s hs => ?_⟩
  · rw [← encP_one, beq_encP, decide_eq_false h2]
  · rw [← encP_permAct, beq_encP, h3 s hs]
    simp

theorem condVK_of {z v : PermMod 7} (h : CondV z v) : condVK (encP z) (encP v) = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [condVK, decP_encP, h1, decide_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, ← encP_mul]
  refine ⟨⟨⟨?_, ?_⟩, fun s hs => ?_⟩, ?_⟩
  · rw [← encP_one, beq_encP, decide_eq_false h2]
  · rw [beq_encP, decide_eq_false h3]
  · rw [← encP_permAct, beq_encP, beq_encP]
    rcases h4 s hs with e | e <;> simp [e]
  · exact h5

theorem concl_of {z v : PermMod 7} (h : conclK (encP z) (encP v) = true) : Concl z v := by
  simp only [conclK, ← encP_mul, beq_encP, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

set_option maxRecDepth 100000 in
theorem classify : ∀ z : PermMod 7, CondZ z → ∀ v : PermMod 7, CondV z v → Concl z v := by
  have hw : allLtK (fun c => !condZK c ||
      allLtK (fun d => !condVK c d || conclK c d) 128) 128 = true := by
    decide +kernel
  intro z hz v hv
  have h1 := allLtK_iff.1 hw (encP z) (encP_lt z)
  rw [condZK_of hz, Bool.not_true, Bool.false_or] at h1
  have h2 := allLtK_iff.1 h1 (encP v) (encP_lt v)
  rw [condVK_of hv, Bool.not_true, Bool.false_or] at h2
  exact concl_of h2

end M7

end CFSG.Quasithin.ModC
