module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ASVolI.ChH

namespace PermElemAb2

open Equiv

variable {α : Type*}

private theorem exists_card_eq_two_pow [Finite α] {E : Subgroup (Perm α)} (hE : IsElemAb2 E) :
    ∃ r : ℕ, Nat.card E = 2 ^ r := by
  have hP : IsPGroup 2 E := fun g => ⟨1, by
    have h := hE.2 (g : Perm α) g.2
    exact Subtype.ext (by simpa using h)⟩
  exact (IsPGroup.iff_card (p := 2)).mp hP

private theorem mem_of_mem_orbit {S : Set α} {E : Subgroup (Perm α)}
    (hfix : ∀ g ∈ E, ∀ x, x ∉ S → g x = x) {a : α} (ha : a ∈ S)
    {y : α} (hy : y ∈ MulAction.orbit E a) : y ∈ S := by
  obtain ⟨g, rfl⟩ := hy
  by_contra hgS
  have h1 : (g : Perm α) ((g : Perm α) a) = (g : Perm α) a := hfix g g.2 _ hgS
  have h2 : (g : Perm α) a = a := (g : Perm α).injective h1
  exact hgS (by simpa [Subgroup.smul_def, h2] using ha)

private theorem apply_eq_of_mem_orbit {E : Subgroup (Perm α)} (hE : IsElemAb2 E) {a : α} {s : Perm α}
    (hs : s ∈ E) (hsa : s a = a) {y : α} (hy : y ∈ MulAction.orbit E a) : s y = y := by
  obtain ⟨g, rfl⟩ := hy
  have hcomm : s * (g : Perm α) = (g : Perm α) * s := hE.1 s hs g g.2
  calc s (g • a) = (s * (g : Perm α)) a := rfl
    _ = ((g : Perm α) * s) a := by rw [hcomm]
    _ = g • a := by simp [Subgroup.smul_def, hsa]

private theorem arith_step {m k : ℕ} (hk : 2 ^ k ≤ m) : (m - 2 ^ k) / 2 + k ≤ m / 2 := by
  rcases k with _ | j
  · simp only [pow_zero] at hk ⊢
    omega
  · have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [h2] at hk ⊢
    omega

theorem card_le_two_pow_half [Finite α] :
    ∀ (m : ℕ) (S : Set α), S.ncard = m → ∀ (E : Subgroup (Perm α)), IsElemAb2 E →
      (∀ g ∈ E, ∀ x, x ∉ S → g x = x) → Nat.card E ≤ 2 ^ (m / 2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hS E hE hfix
    by_cases hSne : S.Nonempty
    · obtain ⟨a, ha⟩ := hSne
      set O : Set α := MulAction.orbit E a with hO
      have hOS : O ⊆ S := fun y hy => mem_of_mem_orbit hfix ha hy
      have hcard : Nat.card (MulAction.stabilizer E a) * O.ncard = Nat.card E := by
        rw [hO, ← MulAction.index_stabilizer E a]
        exact Subgroup.card_mul_index _
      obtain ⟨r, hr⟩ := exists_card_eq_two_pow hE
      have hdvd : O.ncard ∣ 2 ^ r := ⟨Nat.card (MulAction.stabilizer E a), by
        rw [← hr, ← hcard, mul_comm]⟩
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hle : 2 ^ k ≤ m := by
        rw [← hk, ← hS]
        exact Set.ncard_le_ncard hOS
      have hpos : 0 < 2 ^ k := by positivity
      let K : Subgroup (Perm α) := (MulAction.stabilizer E a).map E.subtype
      have hKcard : Nat.card K = Nat.card (MulAction.stabilizer E a) :=
        Subgroup.card_map_of_injective E.subtype_injective
      have hKE : ∀ s ∈ K, s ∈ E := by
        intro s hs
        obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hs
        exact g.2
      have hKfix : ∀ s ∈ K, s a = a := by
        intro s hs
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
        have := MulAction.mem_stabilizer_iff.mp hg
        simpa [Subgroup.smul_def] using this
      have hKab : IsElemAb2 K :=
        ⟨fun x hx y hy => hE.1 x (hKE x hx) y (hKE y hy), fun x hx => hE.2 x (hKE x hx)⟩
      have hKS : ∀ g ∈ K, ∀ x, x ∉ S \ O → g x = x := by
        intro g hg x hx
        by_cases hxS : x ∈ S
        · have hxO : x ∈ O := by
            by_contra h
            exact hx ⟨hxS, h⟩
          exact apply_eq_of_mem_orbit hE (hKE g hg) (hKfix g hg) hxO
        · exact hfix g (hKE g hg) x hxS
      have hSO : (S \ O).ncard = m - 2 ^ k := by
        rw [Set.ncard_diff hOS, hS, hk]
      have hlt : m - 2 ^ k < m := by omega
      have hKle := ih (m - 2 ^ k) hlt (S \ O) hSO K hKab hKS
      calc Nat.card E = Nat.card K * 2 ^ k := by rw [← hcard, hKcard, hk]
        _ ≤ 2 ^ ((m - 2 ^ k) / 2) * 2 ^ k := Nat.mul_le_mul_right _ hKle
        _ = 2 ^ ((m - 2 ^ k) / 2 + k) := by rw [pow_add]
        _ ≤ 2 ^ (m / 2) := Nat.pow_le_pow_right (by norm_num) (arith_step hle)
    ·
      have hS0 : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
      have hEbot : E = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        ext x
        exact hfix g hg x (by simp [hS0])
      have : Nat.card E = 1 := by
        rw [hEbot]
        exact Subgroup.card_bot
      rw [this]
      exact Nat.one_le_two_pow

end PermElemAb2

end CFSG.ASVolI.ChH
