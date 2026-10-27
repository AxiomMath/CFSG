module

public import CFSG.LocalAnalysis.StandardType.GGQTwoE7Core

public section

namespace CFSG.StandardType.GGQ2E8K

@[expose] def digK (v i : ℕ) : ℕ := Nat.mod (Nat.div v (Nat.pow 3 i)) 3

@[expose] def recAdd (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k s => Nat.add s (f k)) n

@[expose] def recSum (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  recAdd (fun k => Nat.mul (g k) (Nat.pow 3 k)) n

@[expose] def bitK (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

theorem digK_eq (v i : ℕ) : digK v i = v / 3 ^ i % 3 := rfl

theorem foldl_range_eq_rec (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun s k => s + f k) 0 = recAdd f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem recSum_eight (g : ℕ → ℕ) : recSum g 8 =
    0 + g 0 * 3 ^ 0 + g 1 * 3 ^ 1 + g 2 * 3 ^ 2 + g 3 * 3 ^ 3 + g 4 * 3 ^ 4 + g 5 * 3 ^ 5 +
      g 6 * 3 ^ 6 + g 7 * 3 ^ 7 := rfl

theorem ofDigits_ofFn_eight (g : ℕ → ℕ) :
    Nat.ofDigits 3 (List.ofFn (fun k : Fin 8 => g (k : ℕ))) = recSum g 8 := by
  rw [recSum_eight]
  simp [List.ofFn_succ, Nat.ofDigits_cons]
  ring

theorem recSum_congr {g g' : ℕ → ℕ} (h : ∀ k, g k = g' k) (n : ℕ) : recSum g n = recSum g' n := by
  have e : g = g' := funext h
  rw [e]

theorem bitK_eq (m i : ℕ) : bitK m i = m.testBit i := by
  have h : Nat.land (Nat.shiftRight m i) 1 = m / 2 ^ i % 2 := by
    change (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitK
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h1 : m / 2 ^ i % 2 = 1
  · rw [h1]
    simp
  · rw [decide_eq_false h1]
    cases hb : Nat.beq (m / 2 ^ i % 2) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h1

theorem ite_eq_rec {k i a b : ℕ} :
    (if k = i then a else b) = Bool.rec (motive := fun _ => ℕ) b a (Nat.beq k i) := by
  by_cases h : k = i
  · rw [if_pos h, h, Nat.beq_refl]
  · rw [if_neg h]
    cases hb : Nat.beq k i
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

end CFSG.StandardType.GGQ2E8K

end
