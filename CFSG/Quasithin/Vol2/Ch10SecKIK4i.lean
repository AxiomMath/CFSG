module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4h

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open Equiv Equiv.Perm Finset
open scoped commutatorElement

theorem card_erase_one (c : Fin 7) : (univ.erase c).card = 6 := by
  rw [card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin]

theorem card_erase_two {a b : Fin 7} (hab : a ≠ b) : ((univ.erase a).erase b).card = 5 := by
  rw [card_erase_of_mem (mem_erase.2 ⟨hab.symm, mem_univ b⟩), card_erase_one]

theorem seven_dvd_of_transitive {Lp : Subgroup (Perm (Fin 7))} (c : Fin 7)
    (h : ∀ x, ∃ σ ∈ Lp, σ c = x) : 7 ∣ Nat.card ↥Lp := by
  have horb : MulAction.orbit ↥Lp c = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, rfl⟩ := h x
    exact ⟨⟨σ, hσ⟩, rfl⟩
  have h1 := MulAction.index_stabilizer ↥Lp c
  rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := Subgroup.index_dvd_card (MulAction.stabilizer ↥Lp c)
  rwa [h1] at h2

variable {Lp P : Subgroup (Perm (Fin 7))}

theorem false_of_one_fixed (hLA : Lp ≤ alternatingGroup (Fin 7)) (h60 : 60 ∣ Nat.card ↥Lp)
    (h9 : ¬ 9 ∣ Nat.card ↥Lp) (hPA : P ≤ alternatingGroup (Fin 7)) (hP : Nat.card ↥P = 8)
    (hPN : P ≤ Subgroup.normalizer (Lp : Set (Perm (Fin 7)))) (c : Fin 7)
    (hc : ∀ σ ∈ Lp, σ c = c) (honly : ∀ x, x ≠ c → ∃ σ ∈ Lp, σ x ≠ x) : False := by
  have hPc : ∀ p ∈ P, p c = c := by
    intro p hp
    by_contra hne
    obtain ⟨σ, hσ, hσx⟩ := honly (p c) hne
    have hpN := hPN hp
    have h1 : p⁻¹ * σ * p⁻¹⁻¹ ∈ Lp :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpN) σ).mp hσ
    rw [inv_inv] at h1
    have h2 := hc _ h1
    simp only [Perm.mul_apply] at h2
    apply hσx
    have h3 := congrArg p h2
    simpa using h3
  set s := univ.erase c with hs
  have hsc : s.card = 6 := card_erase_one c
  set A := altOn s with hA
  have hAs : IsSimpleGroup ↥A := isSimpleGroup_altOn s (by omega)
  have hAc : Nat.card ↥A = 360 := by
    rw [hA, card_altOn s (by omega), hsc]
    decide
  have hfixA : ∀ σ : Perm (Fin 7), σ ∈ alternatingGroup (Fin 7) → σ c = c → σ ∈ A := by
    intro σ hσ hσc
    refine mem_altOn.2 ⟨hσ, fun x hx => ?_⟩
    have : x = c := by simpa [hs] using hx
    rw [this, hσc]
  have hLA' : Lp ≤ A := fun σ hσ => hfixA σ (hLA hσ) (hc σ hσ)
  have hPA' : P ≤ A := fun p hp => hfixA p (hPA hp) (hPc p hp)
  set M := Lp ⊔ P with hM
  have hMA : M ≤ A := sup_le hLA' hPA'
  have hMN : M ≤ Subgroup.normalizer (Lp : Set (Perm (Fin 7))) :=
    sup_le Subgroup.le_normalizer hPN
  have h8 : 8 ∣ Nat.card ↥M := hP ▸ Subgroup.card_dvd_of_le le_sup_right
  have h15 : 15 ∣ Nat.card ↥M :=
    (dvd_trans (show (15 : ℕ) ∣ 60 by norm_num) h60).trans (Subgroup.card_dvd_of_le le_sup_left)
  have hdvd : Nat.card ↥M ∣ 360 := hAc ▸ Subgroup.card_dvd_of_le hMA
  have hMc : Nat.card ↥M = 120 ∨ Nat.card ↥M = 360 := by
    have h120 : 120 ∣ Nat.card ↥M := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h15
    obtain ⟨k, hk⟩ := h120
    rw [hk] at hdvd
    have hk3 : k ∣ 3 := by
      have h360 : (360 : ℕ) = 120 * 3 := by norm_num
      rw [h360] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h
    · left
      rw [hk, h]
    · right
      rw [hk, h]
  rcases hMc with h120 | h360
  ·
    set M' := M.subgroupOf A with hM'
    have hM'c : Nat.card ↥M' = 120 := by
      rw [hM', ← h120]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMA).toEquiv
    have hidx : M'.index = 3 := by
      have := Subgroup.card_mul_index M'
      rw [hM'c, hAc] at this
      omega
    have hcore := Subgroup.index_normalCore_dvd_factorial_index M'
    rw [hidx] at hcore
    rcases hAs.eq_bot_or_eq_top_of_normal M'.normalCore with h | h
    · rw [h, Subgroup.index_bot, hAc] at hcore
      norm_num [Nat.factorial] at hcore
    · have hle : M' = ⊤ := eq_top_iff.2 (h ▸ Subgroup.normalCore_le M')
      rw [hle, Subgroup.index_top] at hidx
      omega
  ·
    have hMeq : M = A := Subgroup.eq_of_le_of_card_ge hMA (by rw [h360, hAc])
    have hLn : (Lp.subgroupOf A).Normal := by
      refine ⟨fun l hl x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      have hxM : (x : Perm (Fin 7)) ∈ M := by rw [hMeq]; exact x.2
      have hxN : (x : Perm (Fin 7)) ∈ Subgroup.normalizer (Lp : Set (Perm (Fin 7))) := hMN hxM
      simpa using (Subgroup.mem_normalizer_iff.mp hxN _).mp hl
    rcases hAs.eq_bot_or_eq_top_of_normal (Lp.subgroupOf A) with h | h
    · have hLbot : Lp = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        have : (⟨σ, hLA' hσ⟩ : ↥A) ∈ Lp.subgroupOf A := Subgroup.mem_subgroupOf.2 hσ
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      rw [hLbot, Subgroup.card_bot] at h60
      norm_num at h60
    · have hLeq : Lp = A := le_antisymm hLA' fun σ hσ =>
        Subgroup.mem_subgroupOf.1 (h ▸ Subgroup.mem_top (⟨σ, hσ⟩ : ↥A))
      apply h9
      rw [hLeq, hAc]
      norm_num

theorem fix_pair_of_perfect (hLA : Lp ≤ alternatingGroup (Fin 7)) (hperf : ⁅Lp, Lp⁆ = Lp)
    (h60 : 60 ∣ Nat.card ↥Lp) (h7 : ¬ 7 ∣ Nat.card ↥Lp) (h9 : ¬ 9 ∣ Nat.card ↥Lp)
    (hPA : P ≤ alternatingGroup (Fin 7)) (hP : Nat.card ↥P = 8)
    (hPN : P ≤ Subgroup.normalizer (Lp : Set (Perm (Fin 7)))) :
    ∃ a b : Fin 7, a ≠ b ∧ ∀ σ ∈ Lp, σ a = a ∧ σ b = b := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5
    ((show (5 : ℕ) ∣ 60 by norm_num).trans h60)
  have hg' : orderOf (g : Perm (Fin 7)) = 5 := by rw [Subgroup.orderOf_coe]; exact hg
  obtain ⟨hcyc, hsupp⟩ := isCycle_of_order_five hg'
  set O := (g : Perm (Fin 7)).support with hO
  have hc2 : (univ \ O).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hsupp]
  obtain ⟨a, b, hab, hab'⟩ := card_eq_two.1 hc2
  have hmemO : ∀ y, y ∈ O ↔ y ≠ a ∧ y ≠ b := by
    intro y
    have h1 : y ∉ O ↔ y = a ∨ y = b := by
      have := congrArg (y ∈ ·) hab'
      simpa using this
    constructor
    · intro hy
      exact ⟨fun h => (h1.2 (Or.inl h)) hy, fun h => (h1.2 (Or.inr h)) hy⟩
    · rintro ⟨ha, hb⟩
      by_contra hy
      rcases h1.1 hy with h | h
      exacts [ha h, hb h]
  have hmoved : ∀ y, y ≠ a → y ≠ b → (g : Perm (Fin 7)) y ≠ y := fun y ha hb =>
    Perm.mem_support.1 ((hmemO y).2 ⟨ha, hb⟩)
  by_cases hfa : ∀ σ ∈ Lp, σ a = a
  · by_cases hfb : ∀ σ ∈ Lp, σ b = b
    · exact ⟨a, b, hab, fun σ hσ => ⟨hfa σ hσ, hfb σ hσ⟩⟩
    · exfalso
      push Not at hfb
      refine false_of_one_fixed hLA h60 h9 hPA hP hPN a hfa fun y hy => ?_
      by_cases hyb : y = b
      · subst hyb
        exact hfb
      · exact ⟨g, g.2, hmoved y hy hyb⟩
  · by_cases hfb : ∀ σ ∈ Lp, σ b = b
    · exfalso
      push Not at hfa
      refine false_of_one_fixed hLA h60 h9 hPA hP hPN b hfb fun y hy => ?_
      by_cases hya : y = a
      · subst hya
        exact hfa
      · exact ⟨g, g.2, hmoved y hya hy⟩
    · exfalso
      push Not at hfa hfb
      by_cases hpair : ∀ σ ∈ Lp, (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b)
      · obtain ⟨σ, hσ, hσa⟩ := hfa
        exact hσa (fix_of_perfect_of_pair hperf hab hpair σ hσ)
      · push Not at hpair
        obtain ⟨x0, hx0⟩ : ∃ x0, x0 ≠ a ∧ x0 ≠ b := by
          obtain ⟨x, hx⟩ := card_pos.1 (show 0 < O.card by rw [hsupp]; norm_num)
          exact ⟨x, (hmemO x).1 hx⟩
        have hreachO : ∀ y, y ≠ a → y ≠ b → ∃ τ ∈ Lp, τ x0 = y := by
          intro y hya hyb
          obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (hmoved x0 hx0.1 hx0.2) (hmoved y hya hyb)
          exact ⟨(g : Perm (Fin 7)) ^ i, Lp.pow_mem g.2 i, hi⟩
        have hstep : ∀ y z, (∃ τ ∈ Lp, τ x0 = y) → (∃ ρ ∈ Lp, ρ z = y) →
            ∃ τ ∈ Lp, τ x0 = z := by
          rintro y z ⟨τ, hτ, rfl⟩ ⟨ρ, hρ, hρz⟩
          refine ⟨ρ⁻¹ * τ, Lp.mul_mem (Lp.inv_mem hρ) hτ, ?_⟩
          rw [Perm.mul_apply, ← hρz]
          exact ρ.symm_apply_apply z
        have hreach_ab : (∃ τ ∈ Lp, τ x0 = a) ∧ (∃ τ ∈ Lp, τ x0 = b) := by
          obtain ⟨σ, hσ, hσ'⟩ := hpair
          obtain ⟨ρa, hρa, hρa'⟩ := hfa
          obtain ⟨ρb, hρb, hρb'⟩ := hfb
          by_cases hσa : σ a = a ∨ σ a = b
          ·
            have hσb := hσ' hσa
            have hb : ∃ τ ∈ Lp, τ x0 = b :=
              hstep _ b (hreachO _ hσb.1 hσb.2) ⟨σ, hσ, rfl⟩
            refine ⟨?_, hb⟩
            by_cases h1 : ρa a = b
            · exact hstep _ a hb ⟨ρa, hρa, h1⟩
            · exact hstep _ a (hreachO _ hρa' h1) ⟨ρa, hρa, rfl⟩
          · push Not at hσa
            have ha : ∃ τ ∈ Lp, τ x0 = a :=
              hstep _ a (hreachO _ hσa.1 hσa.2) ⟨σ, hσ, rfl⟩
            refine ⟨ha, ?_⟩
            by_cases h1 : ρb b = a
            · exact hstep _ b ha ⟨ρb, hρb, h1⟩
            · exact hstep _ b (hreachO _ h1 hρb') ⟨ρb, hρb, rfl⟩
        refine h7 (seven_dvd_of_transitive x0 fun y => ?_)
        by_cases hya : y = a
        · subst hya
          exact hreach_ab.1
        · by_cases hyb : y = b
          · subst hyb
            exact hreach_ab.2
          · exact hreachO y hya hyb

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
