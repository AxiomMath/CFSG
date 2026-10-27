module

public import CFSG.Quasithin.H13.A7Offender

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

local notation "W" => sevenWord

@[expose] def FB1 (u : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W u ≠ 1 → fix3 (W u) (W u) (W u) ≤ 32

instance (u : Bool × Bool × Bool × Bool) : Decidable (FB1 u) := by
  unfold FB1
  infer_instance

theorem fb1 : ∀ u, FB1 u := by
  decide +kernel

@[expose] def FB2 (u w : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 → W w * W w = 1 → W u * W w = W w * W u → W u ≠ 1 → W w ≠ 1 → W w ≠ W u →
    fix3 (W u) (W w) (W w) ≤ 16

instance (u w : Bool × Bool × Bool × Bool) : Decidable (FB2 u w) := by
  unfold FB2
  infer_instance

theorem fb2 : ∀ u w, FB2 u w := by
  decide +kernel

@[expose] def Inv3 (u w x : Bool × Bool × Bool × Bool) : Prop :=
  W u * W u = 1 ∧ W w * W w = 1 ∧ W x * W x = 1 ∧ W u * W w = W w * W u ∧
    W u * W x = W x * W u ∧ W w * W x = W x * W w

instance (u w x : Bool × Bool × Bool × Bool) : Decidable (Inv3 u w x) := by
  unfold Inv3
  infer_instance

@[expose] def Dist3 (u w x : Bool × Bool × Bool × Bool) : Prop :=
  W u ≠ 1 ∧ W w ≠ 1 ∧ W w ≠ W u ∧ W x ≠ 1 ∧ W x ≠ W u ∧ W x ≠ W w ∧ W x ≠ W u * W w

instance (u w x : Bool × Bool × Bool × Bool) : Decidable (Dist3 u w x) := by
  unfold Dist3
  infer_instance

@[expose] def FB3 (u w x : Bool × Bool × Bool × Bool) : Prop :=
  Inv3 u w x → Dist3 u w x → fix3 (W u) (W w) (W x) ≤ 8

instance (u w x : Bool × Bool × Bool × Bool) : Decidable (FB3 u w x) := by
  unfold FB3
  infer_instance

theorem fb3 : ∀ u w x, FB3 u w x := by
  decide +kernel

theorem fix3_one : fix3 1 1 1 = 64 := by
  decide +kernel

theorem card_mul_fixE_le {S : Subgroup (Perm (Fin 7))} (hSP : S ≤ sevenP)
    (hS2 : ∀ σ ∈ S, σ * σ = 1) : Nat.card S * Nat.card (fixE S) ≤ 64 := by
  classical
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hS2 _ (mul_mem ha hb))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hS2 a ha),
      inv_eq_of_mul_eq_one_right (hS2 b hb)] at h1
    exact h1.symm
  have hdvd : Nat.card S ∣ 2 ^ 4 := by
    have := card_dvd_of_le hSP
    rwa [nat_card_sevenP] at this
  have hne16 : Nat.card S ≠ 16 := by
    intro h16
    have hSeq : S = sevenP := eq_of_le_of_card_ge hSP (by rw [h16, nat_card_sevenP])
    have hmem : swap 2 3 * (swap 2 4 * swap 3 5) ∈ S := by
      rw [hSeq, sevenP]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have := hS2 _ hmem
    exact absurd this (by decide)
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hcases : Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 4 ∨ Nat.card S = 8 := by
    interval_cases m <;> simp_all
  have hfix := fun {a b c : Perm (Fin 7)} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) =>
    nat_card_fixE_le (S := (S : Set (Perm (Fin 7)))) ha hb hc
  have hpick1 : 1 < Nat.card S → ∃ s ∈ S, s ≠ 1 := by
    intro hs
    obtain ⟨s, hs, hs1⟩ := exists_mem_not_mem_of_card_lt (S := S)
      ({1} : Finset (Perm (Fin 7))) (by rw [Finset.card_singleton]; omega)
    exact ⟨s, hs, by simpa using hs1⟩
  have hpick2 : ∀ s, 2 < Nat.card S → ∃ b ∈ S, b ≠ 1 ∧ b ≠ s := by
    intro s hs
    obtain ⟨b, hb, hbl⟩ := exists_mem_not_mem_of_card_lt (S := S) {1, s}
      (lt_of_le_of_lt Finset.card_le_two hs)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbl
    exact ⟨b, hb, hbl.1, hbl.2⟩
  have hpick3 : ∀ s b, 4 < Nat.card S → ∃ c ∈ S, c ≠ 1 ∧ c ≠ s ∧ c ≠ b ∧ c ≠ s * b := by
    intro s b hs
    obtain ⟨c, hc, hcl⟩ := exists_mem_not_mem_of_card_lt (S := S) {1, s, b, s * b}
      (lt_of_le_of_lt Finset.card_le_four hs)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcl
    exact ⟨c, hc, hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2⟩
  rcases hcases with h1 | h2 | h4 | h8
  · have h3 := hfix S.one_mem S.one_mem S.one_mem
    rw [fix3_one] at h3
    rw [h1]
    omega
  · obtain ⟨s, hs, hs1⟩ := hpick1 (by omega)
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hs)
    have h3 := fb1 u (hS2 _ hs) hs1
    have h5 := hfix hs hs hs
    rw [h2]
    omega
  · obtain ⟨s, hs, hs1⟩ := hpick1 (by omega)
    obtain ⟨b, hb, hb1, hbs⟩ := hpick2 s (by omega)
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hs)
    obtain ⟨w, rfl⟩ := exists_word_of_mem_sevenP (hSP hb)
    have h3 := fb2 u w (hS2 _ hs) (hS2 _ hb) (hcomm _ hs _ hb) hs1 hb1 hbs
    have h5 := hfix hs hb hb
    rw [h4]
    omega
  · obtain ⟨s, hs, hs1⟩ := hpick1 (by omega)
    obtain ⟨b, hb, hb1, hbs⟩ := hpick2 s (by omega)
    obtain ⟨c, hc, hc1, hcs, hcb, hcsb⟩ := hpick3 s b (by omega)
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP (hSP hs)
    obtain ⟨w, rfl⟩ := exists_word_of_mem_sevenP (hSP hb)
    obtain ⟨x, rfl⟩ := exists_word_of_mem_sevenP (hSP hc)
    have h3 := fb3 u w x ⟨hS2 _ hs, hS2 _ hb, hS2 _ hc, hcomm _ hs _ hb, hcomm _ hs _ hc,
      hcomm _ hb _ hc⟩ ⟨hs1, hb1, hbs, hc1, hcs, hcb, hcsb⟩
    have h5 := hfix hs hb hc
    rw [h8]
    omega

end CFSG.Quasithin.H13.A7
