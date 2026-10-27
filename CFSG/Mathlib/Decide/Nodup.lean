module

public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Equiv.Defs

public section

namespace CFSG.Decide

@[expose] def bitsetNodupAux : List ℕ → ℕ → Bool
  | [], _ => true
  | k :: ks, acc => !acc.testBit k && bitsetNodupAux ks (acc ||| 1 <<< k)

@[expose] def bitsetNodup (l : List ℕ) : Bool := bitsetNodupAux l 0

theorem bitsetNodupAux_sound :
    ∀ (l : List ℕ) (acc : ℕ), bitsetNodupAux l acc = true →
      l.Nodup ∧ ∀ k ∈ l, acc.testBit k = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | k :: ks, acc, h => by
    simp only [bitsetNodupAux, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hk, hks⟩ := h
    obtain ⟨hnd, hbits⟩ := bitsetNodupAux_sound ks _ hks
    refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, hnd⟩, ?_⟩
    · have := hbits k hmem
      simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hk
      · have := hbits j hj
        simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

theorem nodup_of_bitsetNodup_nat {l : List ℕ} (h : bitsetNodup l = true) : l.Nodup :=
  (bitsetNodupAux_sound l 0 h).1

theorem nodup_of_bitsetNodup {α : Type*} {l : List α} (f : α → ℕ)
    (h : bitsetNodup (l.map f) = true) : l.Nodup :=
  (nodup_of_bitsetNodup_nat h).of_map f

@[expose] def digitsKey (m : ℕ) (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => digitsKey m g k * m + g k

@[expose] def finFunKey {n m : ℕ} (f : Fin n → Fin m) : ℕ :=
  digitsKey m (fun i => if h : i < n then (f ⟨i, h⟩ : ℕ) else 0) n

@[expose] def permKey {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := finFunKey (⇑σ)

@[expose] def listKey (m : ℕ) (pos : List ℕ) (t : List ℕ) : ℕ :=
  pos.foldr (fun i acc => t.getD i 0 + m * acc) 0

end CFSG.Decide
