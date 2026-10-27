module

public import CFSG.Quasithin.EmptyFaithful.S143A6Nat
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.S1549D

open CFSG.Quasithin.S143

@[expose] def a6u0 : N6 := ⟨Multiplicative.ofAdd ![1, 1, 0, 0, 0, 0], by decide⟩

@[expose] def invPerm (f : Fin 6 → Fin 6) (hf : ∀ i, f (f i) = i) : Equiv.Perm (Fin 6) :=
  ⟨f, f, hf, hf⟩

@[expose] def a6El : List (Equiv.Perm (Fin 6)) :=
  [1, invPerm ![1, 0, 2, 3, 4, 5] (by decide), invPerm ![0, 1, 3, 2, 5, 4] (by decide),
    invPerm ![0, 1, 4, 5, 2, 3] (by decide), invPerm ![0, 1, 5, 4, 3, 2] (by decide),
    invPerm ![1, 0, 3, 2, 5, 4] (by decide), invPerm ![1, 0, 4, 5, 2, 3] (by decide),
    invPerm ![1, 0, 5, 4, 3, 2] (by decide)]

@[expose] def tabPerm (f g : Fin 6 → Fin 6) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) :
    Equiv.Perm (Fin 6) := ⟨f, g, h1, h2⟩

@[expose] def a6W : List (Equiv.Perm (Fin 6)) :=
  [1, tabPerm ![0, 1, 3, 4, 2, 5] ![0, 1, 4, 2, 3, 5] (by decide) (by decide),
    tabPerm ![0, 1, 3, 5, 4, 2] ![0, 1, 5, 2, 4, 3] (by decide) (by decide),
    tabPerm ![0, 1, 4, 3, 5, 2] ![0, 1, 5, 3, 2, 4] (by decide) (by decide),
    tabPerm ![0, 1, 2, 4, 5, 3] ![0, 1, 2, 5, 3, 4] (by decide) (by decide)]

@[expose] def yfun (t : Fin 6 → Fin 6) (p : Equiv.Perm (Fin 6)) (i : Fin 6) : Fin 6 :=
  t (p (t (p⁻¹ i)))

@[expose] def chk3 (t : Fin 6 → Fin 6) (p : Equiv.Perm (Fin 6)) : Prop :=
  (∃ i : Fin 6, yfun t p i ≠ i) ∧ ∀ i : Fin 6, yfun t p (yfun t p (yfun t p i)) = i

instance (t : Fin 6 → Fin 6) (p : Equiv.Perm (Fin 6)) : Decidable (chk3 t p) := by
  unfold chk3
  infer_instance

set_option maxRecDepth 100000 in
theorem a6_witness : ∀ x : Equiv.Perm (Fin 6), n6Act x a6u0 = a6u0 → x ∈ a6El ∨
    ∃ p ∈ a6W, chk3 ![x 0, x 1, x 2, x 3, x 4, x 5] p := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6_W_ok : ∀ p ∈ a6W, Equiv.Perm.sign p = 1 ∧ n6Act p a6u0 = a6u0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6_singles : ∀ a ∈ a6El, a ≠ 1 →
    (Finset.univ.filter fun v : N6 => n6Act a v = v).card ≤ 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6_pairs : ∀ a ∈ a6El, ∀ b ∈ a6El, a ≠ 1 → b ≠ 1 → a ≠ b →
    (Finset.univ.filter fun v : N6 => n6Act a v = v ∧ n6Act b v = v).card ≤ 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6_full : (Finset.univ.filter fun v : N6 => ∀ a ∈ a6El, n6Act a v = v).card ≤ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6P_card : (Finset.univ.filter fun σ : Equiv.Perm (Fin 6) =>
    Equiv.Perm.sign σ = 1 ∧ n6Act σ a6u0 = a6u0).card = 24 := by
  decide +kernel

theorem chk3_iff (x p : Equiv.Perm (Fin 6)) :
    chk3 ![x 0, x 1, x 2, x 3, x 4, x 5] p ↔
      x * (p * x * p⁻¹) ≠ 1 ∧ (x * (p * x * p⁻¹)) ^ 3 = 1 := by
  have ht : (![x 0, x 1, x 2, x 3, x 4, x 5] : Fin 6 → Fin 6) = ⇑x := by
    funext i
    fin_cases i <;> rfl
  have hy : ∀ i, yfun (![x 0, x 1, x 2, x 3, x 4, x 5] : Fin 6 → Fin 6) p i =
      (x * (p * x * p⁻¹)) i := by
    intro i
    rw [yfun, ht]
    simp [Equiv.Perm.mul_apply]
  unfold chk3
  simp only [hy]
  generalize x * (p * x * p⁻¹) = y
  constructor
  · rintro ⟨⟨i, hi⟩, h3⟩
    refine ⟨fun h => hi (by rw [h]; rfl), ?_⟩
    refine Equiv.ext fun j => ?_
    simpa [pow_succ] using h3 j
  · rintro ⟨h1, h3⟩
    refine ⟨?_, fun j => ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h1 (Equiv.ext hcon)
    · have := congrArg (fun f : Equiv.Perm (Fin 6) => f j) h3
      simpa [pow_succ] using this

theorem eq_one_of_pow_three {Q : Subgroup (Equiv.Perm (Fin 6))}
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1) {y : Equiv.Perm (Fin 6)} (hy : y ∈ Q)
    (h3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hQ2 y hy
  have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hg : orderOf y ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
  have hg1 : Nat.gcd 3 (2 ^ k) = 1 := hcop
  rw [hg1] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem a6_sub_El {Q : Subgroup (Equiv.Perm (Fin 6))} (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hQu : ∀ q ∈ Q, n6Act q a6u0 = a6u0)
    (hQn : ∀ p ∈ alternatingGroup (Fin 6), n6Act p a6u0 = a6u0 → ∀ q ∈ Q, p * q * p⁻¹ ∈ Q)
    {q : Equiv.Perm (Fin 6)} (hq : q ∈ Q) : q ∈ a6El := by
  rcases a6_witness q (hQu q hq) with h | ⟨p, hp, hchk⟩
  · exact h
  · exfalso
    obtain ⟨hsign, hfix⟩ := a6_W_ok p hp
    have hpA : p ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.mpr hsign
    have hconj := hQn p hpA hfix q hq
    have hy : q * (p * q * p⁻¹) ∈ Q := Q.mul_mem hq hconj
    obtain ⟨h1, h3⟩ := (chk3_iff q p).mp hchk
    exact h1 (eq_one_of_pow_three hQ2 hy h3)

theorem card_fix_le {B : Subgroup (Equiv.Perm (Fin 6))} {l : List (Equiv.Perm (Fin 6))}
    (hl : ∀ a ∈ l, a ∈ B) {m : ℕ}
    (h : (Finset.univ.filter fun v : N6 => ∀ a ∈ l, n6Act a v = v).card ≤ m) :
    Nat.card {v : N6 // ∀ b ∈ B, n6Act b v = v} ≤ m := by
  classical
  have hinj : Function.Injective
      (fun v : {v : N6 // ∀ b ∈ B, n6Act b v = v} =>
        (⟨v.1, by simpa using fun a ha => v.2 a (hl a ha)⟩ :
          {v : N6 // v ∈ Finset.univ.filter fun v : N6 => ∀ a ∈ l, n6Act a v = v})) :=
    fun v w hvw => Subtype.ext (by have := congrArg Subtype.val hvw; simpa using this)
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := {v : N6 // v ∈ Finset.univ.filter fun v : N6 =>
    ∀ a ∈ l, n6Act a v = v}), Fintype.card_coe] at h1
  exact h1.trans h

theorem a6_card_bound {Q B : Subgroup (Equiv.Perm (Fin 6))} (hBQ : B ≤ Q)
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1) (hQu : ∀ q ∈ Q, n6Act q a6u0 = a6u0)
    (hQn : ∀ p ∈ alternatingGroup (Fin 6), n6Act p a6u0 = a6u0 → ∀ q ∈ Q, p * q * p⁻¹ ∈ Q)
    (hB1 : B ≠ ⊥) :
    Nat.card B * Nat.card {v : N6 // ∀ b ∈ B, n6Act b v = v} ≤ 16 := by
  classical
  have hBE : ∀ b ∈ B, b ∈ a6El := fun b hb => a6_sub_El hQ2 hQu hQn (hBQ hb)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := fun b => by
    obtain ⟨k, hk⟩ := hQ2 b (hBQ b.2)
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  have hsub : (Finset.univ.filter fun x : Equiv.Perm (Fin 6) => x ∈ B) ⊆ a6El.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact List.mem_toFinset.mpr (hBE x hx.2)
  have hcardB : Nat.card B = (Finset.univ.filter fun x : Equiv.Perm (Fin 6) => x ∈ B).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hle8 : Nat.card B ≤ 8 := by
    rw [hcardB]
    exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  have hne1 : Nat.card B ≠ 1 := by
    intro h1
    exact hB1 ((Subgroup.card_eq_one).mp h1)
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    rw [this] at hn
    exact hne1 (by simpa using hn)
  have hn3 : n ≤ 3 := by
    by_contra h4
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at this
    omega
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
  have hb1' : (b : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hb1 (Subtype.ext h)
  interval_cases n
  ·
    have hsing := a6_singles b (hBE b b.2) hb1'
    have hcf := card_fix_le (B := B) (l := [(b : Equiv.Perm (Fin 6))]) (by simp) (m := 8)
      (by simpa using hsing)
    rw [hn]
    omega
  ·
    have hex : ∃ c : B, c ≠ 1 ∧ c ≠ b := by
      by_contra hcon
      push Not at hcon
      have hsubs : (Finset.univ : Finset B) ⊆ {1, b} := by
        intro c _
        by_cases hc1 : c = 1
        · simp [hc1]
        · simp [hcon c hc1]
      have := Finset.card_le_card hsubs
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
      have h2 := Finset.card_le_two (a := (1 : B)) (b := b)
      omega
    obtain ⟨c, hc1, hcb⟩ := hex
    have hc1' : (c : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hcb' : (b : Equiv.Perm (Fin 6)) ≠ (c : Equiv.Perm (Fin 6)) := fun h => hcb (Subtype.ext h.symm)
    have hpair := a6_pairs b (hBE b b.2) c (hBE c c.2) hb1' hc1' hcb'
    have hcf := card_fix_le (B := B) (l := [(b : Equiv.Perm (Fin 6)), (c : Equiv.Perm (Fin 6))])
      (by simp) (m := 4) (by simpa using hpair)
    rw [hn]
    omega
  ·
    have hall : ∀ e ∈ a6El, e ∈ B := by
      intro e he
      by_contra heB
      have hsub' : (Finset.univ.filter fun x : Equiv.Perm (Fin 6) => x ∈ B) ⊆ a6El.toFinset.erase e := by
        intro x hx
        rw [Finset.mem_filter] at hx
        refine Finset.mem_erase.mpr ⟨fun hxe => heB (hxe ▸ hx.2), List.mem_toFinset.mpr (hBE x hx.2)⟩
      have h1 := Finset.card_le_card hsub'
      have h2 : (a6El.toFinset.erase e).card = a6El.toFinset.card - 1 :=
        Finset.card_erase_of_mem (List.mem_toFinset.mpr he)
      have h3 := List.toFinset_card_le a6El
      have h4 : a6El.length = 8 := by decide
      rw [← hcardB, hn] at h1
      omega
    have hcf := card_fix_le (B := B) (l := a6El) hall (m := 2) a6_full
    rw [hn]
    omega

end CFSG.Quasithin.S1549D
