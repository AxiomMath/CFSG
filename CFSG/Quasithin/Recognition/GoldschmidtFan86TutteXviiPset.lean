module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcDefs
public import Mathlib.Tactic.Group
public import Mathlib.Order.Interval.Finset.Nat

public section

namespace CFSG.Quasithin.Fan86.Tutte.Xvii

variable {H : Type*} [Group H]

structure XviiInput (s : ℕ) (r l : H) (Hs : ℕ → Subgroup H) : Prop where
  abel_sq_eq_one : ∀ {i k : ℕ}, i < s → Abel Hs i → 1 ≤ k → k ≤ i → tx r l k ^ 2 = 1
  abelian_iff : ∀ {i : ℕ}, 1 ≤ i → i < s →
    (Abel Hs i ↔ ∀ k : ℕ, 1 ≤ k → k ≤ i → tx r l k ^ 2 = 1)
  pset_mul : ∀ {i : ℕ}, i < s → Abel Hs i → ∀ {T T' : Finset ℕ}, T ⊆ Finset.Icc 1 i →
    T' ⊆ Finset.Icc 1 i → pset r l T * pset r l T' = pset r l (symmDiff T T')
  sq_support : ∀ {i : ℕ}, 1 ≤ i → i < s → Abel Hs (i - 1) →
    ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 (i - 1) ∧ tx r l i ^ 2 = pset r l T ∧ Even T.card ∧
      ∀ t ∈ T, i - t ∈ T

section Shift

variable (r l : H)

theorem tx_zero : tx r l 0 = 1 := by simp [tx]

theorem shift_conj (a b j : ℤ) :
    r ^ (-j) * ((tx r l a)⁻¹ * tx r l b) * r ^ j = (tx r l (a + j))⁻¹ * tx r l (b + j) := by
  simp only [tx]
  group

theorem shift_x (k j : ℤ) : r ^ (-j) * tx r l k * r ^ j = (tx r l j)⁻¹ * tx r l (k + j) := by
  have := shift_conj r l 0 k j
  rwa [tx_zero, inv_one, one_mul, zero_add] at this

variable {r l}

theorem conj_sq {a : H} (ha : a * a = 1) (g : H) : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := by
  calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
    _ = 1 := by rw [ha]; group

end Shift

section Chain

variable {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem hs_mono (h : IsTutteSys s r l ξ Hs) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ s) :
    Hs a ≤ Hs b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (h.mono b (by omega))

theorem tx_mem_le (h : IsTutteSys s r l ξ Hs) {k n : ℕ} (hk : k ≤ n) (hn : n ≤ s) :
    tx r l k ∈ Hs n :=
  hs_mono h hk hn (h.x_mem k (by omega))

theorem tx_comm (h : IsTutteSys s r l ξ Hs) {n : ℕ} (hn : n ≤ s) (hab : Abel Hs n) {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) : tx r l a * tx r l b = tx r l b * tx r l a :=
  hab _ (tx_mem_le h ha hn) _ (tx_mem_le h hb hn)

end Chain

section Pset

variable {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem pset_empty : pset r l ∅ = 1 := by simp [pset]

theorem pset_singleton (a : ℕ) : pset r l {a} = tx r l a := by simp [pset]

theorem symmDiff_singleton_of_notMem {a : ℕ} {U : Finset ℕ} (haU : a ∉ U) :
    symmDiff {a} U = insert a U := by
  ext x
  by_cases hx : x = a <;> simp [hx, haU, symmDiff_def]

variable (B : XviiInput s r l Hs) {n : ℕ} (hn : n < s) (hab : Abel Hs n)
include B hn hab

theorem pset_insert {a : ℕ} {U : Finset ℕ} (ha : a ∈ Finset.Icc 1 n) (hU : U ⊆ Finset.Icc 1 n)
    (haU : a ∉ U) : pset r l (insert a U) = tx r l a * pset r l U := by
  have h1 := B.pset_mul hn hab (T := {a}) (T' := U) (Finset.singleton_subset_iff.2 ha) hU
  rw [pset_singleton, symmDiff_singleton_of_notMem haU] at h1
  exact h1.symm

theorem pset_mul_self {U : Finset ℕ} (hU : U ⊆ Finset.Icc 1 n) :
    pset r l U * pset r l U = 1 := by
  rw [B.pset_mul hn hab hU hU, symmDiff_self, Finset.bot_eq_empty, pset_empty]

theorem pset_mem (h : IsTutteSys s r l ξ Hs) :
    ∀ U : Finset ℕ, U ⊆ Finset.Icc 1 n → pset r l U ∈ Hs n := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro _
    rw [pset_empty]
    exact one_mem _
  | insert a U haU ih =>
    intro hsub
    have hUsub : U ⊆ Finset.Icc 1 n := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haI : a ∈ Finset.Icc 1 n := hsub (Finset.mem_insert_self a U)
    rw [pset_insert B hn hab haI hUsub haU]
    exact mul_mem (tx_mem_le h (Finset.mem_Icc.1 haI).2 hn.le) (ih hUsub)

theorem pset_conj {g : H} :
    ∀ U : Finset ℕ, U ⊆ Finset.Icc 1 n → (∀ c ∈ U, tx r l c * g = g⁻¹ * tx r l c) →
      (Even U.card → pset r l U * g = g * pset r l U) ∧
      (Odd U.card → pset r l U * g = g⁻¹ * pset r l U) := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨fun _ => by rw [pset_empty]; group, fun h => ?_⟩
    simp at h
  | insert a U haU ih =>
    intro hsub hc
    have hUsub : U ⊆ Finset.Icc 1 n := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haI : a ∈ Finset.Icc 1 n := hsub (Finset.mem_insert_self a U)
    have hca : tx r l a * g = g⁻¹ * tx r l a := hc a (Finset.mem_insert_self a U)
    have hca' : tx r l a * g⁻¹ = g * tx r l a := by
      have h1 : g * (tx r l a * g) = tx r l a := by rw [hca]; group
      calc tx r l a * g⁻¹ = (g * (tx r l a * g)) * g⁻¹ := by rw [h1]
        _ = g * tx r l a := by group
    obtain ⟨hev, hod⟩ := ih hUsub (fun c hcU => hc c (Finset.mem_insert_of_mem hcU))
    rw [pset_insert B hn hab haI hUsub haU, Finset.card_insert_of_notMem haU]
    refine ⟨fun hE => ?_, fun hO => ?_⟩
    · have hodd : Odd U.card := by
        rw [Nat.even_add_one] at hE
        exact Nat.not_even_iff_odd.1 hE
      rw [mul_assoc, hod hodd, ← mul_assoc, hca', mul_assoc]
    · have heven : Even U.card := by
        rw [Nat.odd_add_one] at hO
        exact Nat.not_odd_iff_even.1 hO
      rw [mul_assoc, hev heven, ← mul_assoc, hca, mul_assoc]

theorem shift_pset (h : IsTutteSys s r l ξ Hs) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ n)
    (hx : tx r l m * tx r l m = 1) :
    ∀ U : Finset ℕ, U ⊆ Finset.Icc 1 (n - m) →
      r ^ (-(m : ℤ)) * pset r l U * r ^ (m : ℤ) =
        tx r l m ^ U.card * pset r l (U.image (· + m)) := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro _
    simp [pset_empty]
  | insert a U haU ih =>
    intro hsub
    have hUsub : U ⊆ Finset.Icc 1 (n - m) := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haI : a ∈ Finset.Icc 1 (n - m) := hsub (Finset.mem_insert_self a U)
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.1 haI
    have hIn : a ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨ha1, by omega⟩
    have hUn : U ⊆ Finset.Icc 1 n := fun x hx => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (hUsub hx)
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
    have hamI : a + m ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hUm : U.image (· + m) ⊆ Finset.Icc 1 n := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (hUsub hu)
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hamU : a + m ∉ U.image (· + m) := by
      intro hmem
      obtain ⟨u, hu, hua⟩ := Finset.mem_image.1 hmem
      have : u = a := by omega
      exact haU (this ▸ hu)
    rw [Finset.image_insert, pset_insert B hn hab hamI hUm hamU, Finset.card_insert_of_notMem haU,
      pset_insert B hn hab hIn hUn haU]
    have e1 : r ^ (-(m : ℤ)) * (tx r l a * pset r l U) * r ^ (m : ℤ)
        = (r ^ (-(m : ℤ)) * tx r l a * r ^ (m : ℤ)) *
          (r ^ (-(m : ℤ)) * pset r l U * r ^ (m : ℤ)) := by group
    have hcast : (((a + m : ℕ)) : ℤ) = (a : ℤ) + (m : ℤ) := by push_cast; ring
    have hinv : (tx r l (m : ℤ))⁻¹ = tx r l m := inv_eq_of_mul_eq_one_right hx
    have hc : Commute (tx r l ((a + m : ℕ) : ℤ)) (tx r l (m : ℤ)) :=
      tx_comm h hn.le hab (Finset.mem_Icc.1 hamI).2 hm
    rw [e1, ih hUsub, shift_x r l (a : ℤ) (m : ℤ), hinv, hcast]
    have hc' : tx r l ((a : ℤ) + m) * tx r l (m : ℤ) ^ U.card =
        tx r l (m : ℤ) ^ U.card * tx r l ((a : ℤ) + m) := by
      have := (hc.pow_right U.card).eq
      rwa [hcast] at this
    calc tx r l m * tx r l ((a : ℤ) + m) *
          (tx r l m ^ U.card * pset r l (U.image (· + m)))
        = tx r l m * (tx r l ((a : ℤ) + m) * tx r l m ^ U.card) * pset r l (U.image (· + m)) := by
          group
      _ = tx r l m * (tx r l m ^ U.card * tx r l ((a : ℤ) + m)) * pset r l (U.image (· + m)) := by
          rw [hc']
      _ = tx r l m ^ (U.card + 1) * (tx r l ((a : ℤ) + m) * pset r l (U.image (· + m))) := by
          group

end Pset

end CFSG.Quasithin.Fan86.Tutte.Xvii
