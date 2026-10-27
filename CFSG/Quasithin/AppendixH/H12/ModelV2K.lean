module

public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.Quasithin.AppendixH.H12.ModelV2K

@[expose] noncomputable def forceM {α : Type} (y : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem forceM_apply {α : Type} (y : ℕ) (k : ℕ → α) : forceM y k = k y := by
  cases y <;> rfl

@[expose] def bitM (m x : ℕ) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 x))

theorem bitM_eq (m x : ℕ) : bitM m x = m.testBit x := by
  have h : Nat.land m (Nat.shiftLeft 1 x) = if m.testBit x then 2 ^ x else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (m &&& (1 <<< x)).testBit i = _
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hb : m.testBit x
    · rw [if_pos hb, Nat.testBit_two_pow]
      by_cases hi : x = i
      · subst hi
        simp [hb]
      · simp [hi]
    · rw [if_neg hb, Nat.zero_testBit]
      by_cases hi : x = i
      · subst hi
        simp [hb]
      · simp [hi]
  unfold bitM
  rw [h]
  by_cases hb : m.testBit x
  · rw [if_pos hb, hb]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos x)
  · have hf : m.testBit x = false := by simpa using hb
    rw [if_neg hb, hf]
    rfl

@[expose] noncomputable def nodupMK (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih m => Bool.rec (motive := fun _ => Bool)
      (forceM (Nat.lor m (Nat.shiftLeft 1 x)) ih) false (bitM m x)) L

theorem nodup_of_nodupMK' : ∀ (L : List ℕ) (m : ℕ), nodupMK L m = true →
    L.Nodup ∧ ∀ x ∈ L, m.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: xs, m, h => by
    change Bool.rec (motive := fun _ => Bool)
      (forceM (Nat.lor m (Nat.shiftLeft 1 x)) (nodupMK xs)) false (bitM m x) = true at h
    cases hb : bitM m x
    · rw [hb, forceM_apply] at h
      obtain ⟨ih1, ih2⟩ := nodup_of_nodupMK' xs _ h
      have hx : m.testBit x = false := by rw [← bitM_eq, hb]
      have hor : ∀ y, (Nat.lor m (Nat.shiftLeft 1 x)).testBit y = (m.testBit y || decide (x = y)) :=
        fun y => by
          change (m ||| (1 <<< x)).testBit y = _
          rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, ih1⟩, fun y hy => ?_⟩
      · have h1 := ih2 x hmem
        rw [hor] at h1
        simp at h1
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · have h1 := ih2 y hy
          rw [hor] at h1
          exact (Bool.or_eq_false_iff.1 h1).1
    · rw [hb] at h
      exact absurd h Bool.false_ne_true

theorem nodup_of_nodupMK {L : List ℕ} (h : nodupMK L 0 = true) : L.Nodup :=
  (nodup_of_nodupMK' L 0 h).1

end CFSG.Quasithin.AppendixH.H12.ModelV2K

end
