module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4i
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open Equiv Equiv.Perm Finset

theorem not_mem_erase_two {a b x : Fin 7} : x ∉ (univ.erase a).erase b ↔ x = a ∨ x = b := by
  simp only [mem_erase, mem_univ, and_true, not_and, not_not]
  constructor
  · intro h
    by_cases hxb : x = b
    · exact Or.inr hxb
    · exact Or.inl (h hxb)
  · rintro (h | h) hxb
    · exact h
    · exact absurd h hxb

theorem mem_iff_of_fix {Lp : Subgroup (Perm (Fin 7))} (hLA : Lp ≤ alternatingGroup (Fin 7))
    (h60 : 60 ∣ Nat.card ↥Lp) {a b : Fin 7} (hab : a ≠ b)
    (hfix : ∀ σ ∈ Lp, σ a = a ∧ σ b = b) (σ : Perm (Fin 7)) :
    σ ∈ Lp ↔ (σ ∈ alternatingGroup (Fin 7) ∧ σ a = a ∧ σ b = b) := by
  set s := (univ.erase a).erase b with hs
  have hle : Lp ≤ altOn s := fun τ hτ => mem_altOn.2 ⟨hLA hτ, fun x hx => by
    rcases not_mem_erase_two.1 hx with rfl | rfl
    exacts [(hfix τ hτ).1, (hfix τ hτ).2]⟩
  have hcard : Nat.card ↥(altOn s) = 60 := by
    rw [card_altOn s (by rw [card_erase_two hab]; norm_num), card_erase_two hab]
    decide
  have heq : Lp = altOn s := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos h60)
  rw [heq, mem_altOn]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 a (not_mem_erase_two.2 (Or.inl rfl)), h2 b (not_mem_erase_two.2 (Or.inr rfl))⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx => ?_⟩
    rcases not_mem_erase_two.1 hx with rfl | rfl
    exacts [h2, h3]

theorem threeCycle_inv_apply {p q r : Fin 7} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (swap p q * swap p r)⁻¹ p = q ∧ (swap p q * swap p r)⁻¹ q = r ∧
      (swap p q * swap p r)⁻¹ r = p := by
  rw [mul_inv_rev, swap_inv, swap_inv]
  simp only [Perm.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [swap_apply_left, swap_apply_of_ne_of_ne hpq.symm hqr]
  · rw [swap_apply_right, swap_apply_left]
  · rw [swap_apply_of_ne_of_ne hpr.symm hqr.symm, swap_apply_right]

theorem exists_threeCycle_fix {a b : Fin 7} (hab : a ≠ b) (x : Fin 7 → ZMod 2) :
    ∃ c : Perm (Fin 7), c.IsThreeCycle ∧ c a = a ∧ c b = b ∧ ∀ i, x (c⁻¹ i) = x i := by
  classical
  set O := (univ.erase a).erase b with hO
  have hOc : O.card = 5 := card_erase_two hab
  have hsum := card_filter_add_card_filter_not (s := O) (fun i => x i = 0)
  rw [hOc] at hsum
  have key : ∃ v : ZMod 2, 2 < (O.filter fun i => x i = v).card := by
    by_cases h0 : 2 < (O.filter fun i => x i = 0).card
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have heq : (O.filter fun i => ¬ x i = 0) = O.filter fun i => x i = 1 := by
        apply filter_congr
        intro i _
        constructor
        · intro h
          have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          exact this _ h
        · intro h
          rw [h]
          decide
      rw [← heq]
      omega
  obtain ⟨v, hv⟩ := key
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := two_lt_card.1 hv
  simp only [mem_filter, hO, mem_erase, mem_univ, and_true] at hp hq hr
  refine ⟨swap p q * swap p r, isThreeCycle_swap_mul_swap_same hpq hpr hqr, ?_, ?_, fun i => ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hp.1.2) (Ne.symm hr.1.2),
      swap_apply_of_ne_of_ne (Ne.symm hp.1.2) (Ne.symm hq.1.2)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hp.1.1) (Ne.symm hr.1.1),
      swap_apply_of_ne_of_ne (Ne.symm hp.1.1) (Ne.symm hq.1.1)]
  · obtain ⟨h1, h2, h3⟩ := threeCycle_inv_apply hpq hpr hqr
    by_cases hip : i = p
    · subst hip
      rw [h1, hp.2, hq.2]
    · by_cases hiq : i = q
      · subst hiq
        rw [h2, hq.2, hr.2]
      · by_cases hir : i = r
        · subst hir
          rw [h3, hr.2, hp.2]
        · rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply,
            swap_apply_of_ne_of_ne hip hiq, swap_apply_of_ne_of_ne hip hir]

theorem exists_threeCycle_move {a b y : Fin 7} (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    ∃ c : Perm (Fin 7), c.IsThreeCycle ∧ c a = a ∧ c b = b ∧ c y ≠ y := by
  classical
  set O := (((univ.erase a).erase b).erase y) with hO
  have hOc : O.card = 4 := by
    rw [hO, card_erase_of_mem, card_erase_two hab]
    simp [hya, hyb]
  obtain ⟨q, hq, r, hr, hqr⟩ := one_lt_card.1 (show 1 < O.card by omega)
  simp only [hO, mem_erase, mem_univ, and_true] at hq hr
  refine ⟨swap y q * swap y r, isThreeCycle_swap_mul_swap_same (Ne.symm hq.1) (Ne.symm hr.1) hqr,
    ?_, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hya) (Ne.symm hr.2.2),
      swap_apply_of_ne_of_ne (Ne.symm hya) (Ne.symm hq.2.2)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hyb) (Ne.symm hr.2.1),
      swap_apply_of_ne_of_ne (Ne.symm hyb) (Ne.symm hq.2.1)]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hr.1 (Ne.symm hqr)]
    exact hr.1

theorem mem_of_normalizes {Lp : Subgroup (Perm (Fin 7))} (hLA : Lp ≤ alternatingGroup (Fin 7))
    (h60 : 60 ∣ Nat.card ↥Lp) {a b : Fin 7} (hab : a ≠ b)
    (hfix : ∀ σ ∈ Lp, σ a = a ∧ σ b = b) {γ : Perm (Fin 7)}
    (hγA : γ ∈ alternatingGroup (Fin 7)) (hγ3 : γ ^ 3 = 1)
    (hγN : γ ∈ Subgroup.normalizer (Lp : Set (Perm (Fin 7)))) : γ ∈ Lp := by
  have hmem := mem_iff_of_fix hLA h60 hab hfix
  have hfixpts : ∀ y, (∀ σ ∈ Lp, σ y = y) → y = a ∨ y = b := by
    intro y hy
    by_contra h
    push Not at h
    obtain ⟨c, hc, hca, hcb, hcy⟩ := exists_threeCycle_move hab h.1 h.2
    exact hcy (hy c ((hmem c).2 ⟨hc.mem_alternatingGroup, hca, hcb⟩))
  have himg : ∀ y, (∀ σ ∈ Lp, σ y = y) → ∀ σ ∈ Lp, σ (γ y) = γ y := by
    intro y hy σ hσ
    have h1 : γ⁻¹ * σ * γ⁻¹⁻¹ ∈ Lp :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hγN) σ).mp hσ
    rw [inv_inv] at h1
    have h2 := hy _ h1
    simp only [Perm.mul_apply] at h2
    have h3 := congrArg γ h2
    simpa using h3
  have hγa := hfixpts _ (himg a fun σ hσ => (hfix σ hσ).1)
  have hγb := hfixpts _ (himg b fun σ hσ => (hfix σ hσ).2)
  have hγ3' : ∀ y, γ (γ (γ y)) = y := by
    intro y
    have := congrArg (fun f : Perm (Fin 7) => f y) hγ3
    simpa [pow_succ, Perm.mul_apply] using this
  refine (hmem γ).2 ⟨hγA, ?_⟩
  rcases hγa with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases hγb with h2 | h2
    · exact absurd (γ.injective (h2.trans h1.symm)) hab.symm
    · exact h2
  · exfalso
    rcases hγb with h2 | h2
    · have := hγ3' a
      rw [h1, h2, h1] at this
      exact hab this.symm
    · exact hab (γ.injective (h1.trans h2.symm))

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
