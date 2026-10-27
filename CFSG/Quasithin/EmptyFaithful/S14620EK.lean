module

public import CFSG.Permutation.FinPackCount
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Action.End

public section

namespace CFSG.Quasithin.S14620EK

open Equiv Finset CFSG.Permutation.FinPack
open scoped Pointwise

@[expose] def andB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

theorem andB_eq (x y : Bool) : andB x y = true ↔ x = true ∧ y = true := by
  cases x <;> cases y <;> decide

@[expose] noncomputable def qA (c : ℕ) : Bool :=
  andB (Nat.ble 4 (rd c 4)) (andB (Nat.ble 4 (rd c 5)) (Nat.ble 4 (rd c 6)))

@[expose] noncomputable def qB (c : ℕ) : Bool :=
  andB (Nat.beq (Nat.shiftRight (rd c 0) 1) (Nat.shiftRight (rd c 1) 1))
    (andB (Nat.beq (Nat.shiftRight (rd c 2) 1) (Nat.shiftRight (rd c 3) 1))
      (andB (Nat.beq (Nat.shiftRight (rd c 4) 1) (Nat.shiftRight (rd c 5) 1))
        (Nat.beq (rd c 6) 6)))

@[expose] noncomputable def qAB (c : ℕ) : Bool := andB (qA c) (qB c)

theorem cnt_a : cntK 7 qA 7 0 0 0 = 144 := by decide +kernel

theorem cnt_b : cntK 7 qB 7 0 0 0 = 48 := by decide +kernel

theorem cnt_ab : cntK 7 qAB 7 0 0 0 = 16 := by decide +kernel

theorem smul_eq_iff {G α : Type*} [Group G] [MulAction G α] [DecidableEq α] (g : G)
    (s : Finset α) : g • s = s ↔ ∀ x ∈ s, g • x ∈ s := by
  constructor
  · intro h x hx
    rw [← h]
    exact Finset.smul_mem_smul_finset hx
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
      exact h x hx
    · rw [Finset.card_smul_finset]

section Lanes

variable (g : Perm (Fin 7))

theorem rd0 : rd (enc g) 0 = (g 0 : ℕ) := rd_enc (by norm_num) g 0
theorem rd1 : rd (enc g) 1 = (g 1 : ℕ) := rd_enc (by norm_num) g 1
theorem rd2 : rd (enc g) 2 = (g 2 : ℕ) := rd_enc (by norm_num) g 2
theorem rd3 : rd (enc g) 3 = (g 3 : ℕ) := rd_enc (by norm_num) g 3
theorem rd4 : rd (enc g) 4 = (g 4 : ℕ) := rd_enc (by norm_num) g 4
theorem rd5 : rd (enc g) 5 = (g 5 : ℕ) := rd_enc (by norm_num) g 5
theorem rd6 : rd (enc g) 6 = (g 6 : ℕ) := rd_enc (by norm_num) g 6

end Lanes

theorem mem_A_iff : ∀ y : Fin 7, y ∈ ({4, 5, 6} : Finset (Fin 7)) ↔ 4 ≤ y.val := by decide

theorem stabA_iff (g : Perm (Fin 7)) :
    g • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6} ↔ qA (enc g) = true := by
  rw [smul_eq_iff, qA, andB_eq, andB_eq, Nat.ble_eq, Nat.ble_eq, Nat.ble_eq, rd4, rd5, rd6]
  constructor
  · intro h
    exact ⟨(mem_A_iff _).1 (h 4 (by decide)), (mem_A_iff _).1 (h 5 (by decide)),
      (mem_A_iff _).1 (h 6 (by decide))⟩
  · rintro ⟨h4, h5, h6⟩ x hx
    rw [Perm.smul_def, mem_A_iff]
    have hx' : x = 4 ∨ x = 5 ∨ x = 6 := by simpa using hx
    rcases hx' with rfl | rfl | rfl
    · exact h4
    · exact h5
    · exact h6

@[expose] def partB : Finset (Finset (Fin 7)) := {{0, 1}, {2, 3}, {4, 5}, {6}}

theorem pair_mem_iff : ∀ a b : Fin 7, a ≠ b → (({a, b} : Finset (Fin 7)) ∈ partB ↔
    a.val / 2 = b.val / 2) := by
  decide

theorem single_mem_iff : ∀ a : Fin 7, ({a} : Finset (Fin 7)) ∈ partB ↔ a.val = 6 := by decide

theorem shr1 (m : ℕ) : Nat.shiftRight m 1 = m / 2 := by
  change m >>> 1 = _
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem pair_smul (g : Perm (Fin 7)) {a b : Fin 7} (hab : a ≠ b) :
    (g • ({a, b} : Finset (Fin 7)) ∈ partB ↔ (g a).val / 2 = (g b).val / 2) := by
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, Perm.smul_def, Perm.smul_def]
  exact pair_mem_iff (g a) (g b) fun h => hab (g.injective h)

theorem single_smul (g : Perm (Fin 7)) (a : Fin 7) :
    (g • ({a} : Finset (Fin 7)) ∈ partB ↔ (g a).val = 6) := by
  rw [Finset.smul_finset_singleton, Perm.smul_def]
  exact single_mem_iff (g a)

theorem stabB_iff (g : Perm (Fin 7)) : g • partB = partB ↔ qB (enc g) = true := by
  rw [smul_eq_iff, qB, andB_eq, andB_eq, andB_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq,
    shr1, shr1, shr1, shr1, shr1, shr1, rd0, rd1, rd2, rd3, rd4, rd5, rd6,
    ← pair_smul g (a := 0) (b := 1) (by decide), ← pair_smul g (a := 2) (b := 3) (by decide),
    ← pair_smul g (a := 4) (b := 5) (by decide), ← single_smul g 6]
  constructor
  · intro h
    exact ⟨h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide)⟩
  · rintro ⟨h1, h2, h3, h4⟩ x hx
    have hx' : x = {0, 1} ∨ x = {2, 3} ∨ x = {4, 5} ∨ x = {6} := by simpa [partB] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

theorem qAB_iff (g : Perm (Fin 7)) :
    (g • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6} ∧ g • partB = partB) ↔ qAB (enc g) = true := by
  rw [qAB, andB_eq, ← stabA_iff, ← stabB_iff]

theorem card_a : (univ.filter fun g : Perm (Fin 7) => qA (enc g) = true).card = 144 := by
  rw [card_filter_eq_cntK, cnt_a]

theorem card_b : (univ.filter fun g : Perm (Fin 7) => qB (enc g) = true).card = 48 := by
  rw [card_filter_eq_cntK, cnt_b]

theorem card_ab : (univ.filter fun g : Perm (Fin 7) => qAB (enc g) = true).card = 16 := by
  rw [card_filter_eq_cntK, cnt_ab]

end CFSG.Quasithin.S14620EK
