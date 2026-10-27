module

public import CFSG.Quasithin.H13.L32AC47k

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt6

open Equiv Equiv.Perm

theorem order_five_fact : ∀ y : Perm (Fin 6), sign y = 1 → y ^ 3 = 1 → y ≠ 1 →
    ¬ (∀ e ∈ e1List, y * e * y⁻¹ ∈ e1List) → ¬ (∀ e ∈ e2List, y * e * y⁻¹ ∈ e2List) →
    ∃ d ∈ d0List, (y * d) ^ 5 = 1 ∧ y * d ≠ 1 := by
  decide +kernel

theorem eps_y0_fixed : ∃ i, CFSG.QuasithinUnique.Ch1.AltSix.epsFun y0 i = i := by
  decide +kernel

theorem x0_eq : x0 = swap 0 1 * swap 1 2 := by
  decide +kernel

theorem six_le_index {Y : Subgroup A6} (hY : Y ≠ ⊤) : 6 ≤ Y.index := by
  by_contra hlt
  push Not at hlt
  have hd := Y.index_normalCore_dvd_factorial_index
  have hsimple : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with hb | ht
  · rw [hb, Subgroup.index_bot, card_A6] at hd
    have h120 : Y.index.factorial ∣ 120 :=
      (Nat.factorial_dvd_factorial (show Y.index ≤ 5 by omega)).trans (by norm_num [Nat.factorial])
    have := Nat.le_of_dvd (by norm_num) (hd.trans h120)
    omega
  · exact hY (eq_top_iff.mpr (ht ▸ Y.normalCore_le))

theorem not_five_dvd_of_isTwoThree {n : ℕ} (h : IsTwoThree n) : ¬ 5 ∣ n := by
  obtain ⟨a, b, rfl⟩ := h
  intro h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h5 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_three).mp
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega

theorem eq_N_of_isTwoThree {Q : Subgroup A6} (hDQ : D0 ≤ Q) (h23 : IsTwoThree (Nat.card Q))
    {r : A6} (hrQ : r ∈ Q) (hr : orderOf r = 3) : Q = N1 ∨ Q = N2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hr3 : (r : Perm (Fin 6)) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr] at h
    have := congrArg Subtype.val h
    simpa using this
  have hr1 : (r : Perm (Fin 6)) ≠ 1 := fun h => by
    have : r = 1 := Subtype.ext h
    rw [this, orderOf_one] at hr
    omega
  have hN : r ∈ N1 ∨ r ∈ N2 := by
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2⟩ := hno
    obtain ⟨d, hd, hd5, hd1⟩ := order_five_fact r (mem_alternatingGroup.mp r.2) hr3 hr1
      (fun h => h1 (mem_N1_of h)) (fun h => h2 (mem_N2_of h))
    have hdA : toA6 d (d0_sign d hd) ∈ Q := hDQ ((mem_D0 (g := toA6 d (d0_sign d hd))).mpr hd)
    have ho : orderOf (⟨r * toA6 d (d0_sign d hd), Q.mul_mem hrQ hdA⟩ : Q) = 5 := by
      rw [Subgroup.orderOf_mk, orderOf_eq_prime_iff]
      exact ⟨Subtype.ext hd5, fun h => hd1 (congrArg Subtype.val h)⟩
    exact not_five_dvd_of_isTwoThree h23 (ho ▸ orderOf_dvd_natCard _)
  have hrD : r ∉ D0 := by
    intro hrD
    obtain ⟨n, hn⟩ := (IsPGroup.of_card (n := 3) (card_D0.trans (by norm_num)) :
      IsPGroup 2 D0) ⟨r, hrD⟩
    have hrn : r ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have h3 := orderOf_dvd_of_pow_eq_one hrn
    rw [hr] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have key : ∀ N : Subgroup A6, Nat.card N = 24 → D0 ≤ N → r ∈ N → Q = N := by
    intro N hN24 hDN hrN
    have hDr : D0 ⊔ Subgroup.zpowers r = N := by
      rcases CFSG.Quasithin.H13.A6.eq_or_eq_of_index_three
          (le_sup_left : D0 ≤ D0 ⊔ Subgroup.zpowers r)
          (sup_le hDN (Subgroup.zpowers_le.mpr hrN)) (by rw [hN24, card_D0]) with h | h
      · exact absurd (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers r) : r ∈ D0) hrD
      · exact h
    have hNQ : N ≤ Q := hDr ▸ sup_le hDQ (Subgroup.zpowers_le.mpr hrQ)
    have h24 : 24 ∣ Nat.card Q := hN24 ▸ Subgroup.card_dvd_of_le hNQ
    have hdvd : Nat.card Q ∣ 360 := card_A6 ▸ Subgroup.card_subgroup_dvd_card Q
    obtain ⟨k, hk⟩ := h24
    have hk15 : k ∣ 15 := by
      obtain ⟨m, hm⟩ := hdvd
      have h1 : 24 * (k * m) = 24 * 15 := by rw [← mul_assoc, ← hk, ← hm]
      exact ⟨m, (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm⟩
    have hk' : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 15 := by
      have := Nat.le_of_dvd (by norm_num) hk15
      interval_cases k <;> omega
    rcases hk' with rfl | rfl | rfl | rfl
    · exact (Subgroup.eq_of_le_of_card_ge hNQ (by omega)).symm
    · exfalso
      have hidx : Q.index = 5 := by
        have := Q.card_mul_index
        rw [hk, card_A6] at this
        omega
      have hQ : Q ≠ ⊤ := fun h => by
        rw [h, Subgroup.card_top, card_A6] at hk
        omega
      have := six_le_index hQ
      omega
    · exact absurd (hk ▸ (by norm_num) : 5 ∣ Nat.card Q) (not_five_dvd_of_isTwoThree h23)
    · exact absurd (hk ▸ (by norm_num) : 5 ∣ Nat.card Q) (not_five_dvd_of_isTwoThree h23)
  rcases hN with h | h
  · exact Or.inl (key N1 card_N1 D0_le_N1 h)
  · exact Or.inr (key N2 card_N2 D0_le_N2 h)

theorem mem_range_conjNormal_of_normalizes
    (β : MulAut A6)
    (hN : (∀ n ∈ N1, β n ∈ N1) ∨ ∀ n ∈ N2, β n ∈ N2) :
    β ∈ (MulAut.conjNormal : Perm (Fin 6) →* MulAut A6).range := by
  obtain ⟨σ, b, hσb⟩ := CFSG.QuasithinUnique.Ch1.AltSix.autOf_surjective β
  cases b
  · exact ⟨σ, hσb⟩
  · exfalso
    rcases hN with hN | hN
    ·
      have hx := hN _ x0_mem_N1
      obtain ⟨i, hi⟩ := fixed_of_normalizes_E1 ((β xA : A6) : Perm (Fin 6))
        (by
          have : β xA ^ 3 = 1 := by
            rw [← map_pow, show xA ^ 3 = 1 from Subtype.ext x0_y0_facts.2.1, map_one]
          exact congrArg Subtype.val this)
        (fun h => x0_y0_facts.2.2.1 (by
          have h' : β xA = β 1 := by rw [map_one]; exact Subtype.ext h
          exact congrArg Subtype.val (β.injective h')))
        (mem_N1_iff.mp hx)
      rw [← hσb, CFSG.QuasithinUnique.Ch1.AltSix.autOf_apply,
        CFSG.QuasithinUnique.Ch1.AltSix.phi_true] at hi
      have hsupp := CFSG.QuasithinUnique.Ch1.AltSix.support_epsPerm_threeCycle
      rw [← x0_eq] at hsupp
      have hj : CFSG.QuasithinUnique.Ch1.AltSix.epsPerm x0 (σ⁻¹ i) = σ⁻¹ i := by
        have := congrArg (fun j => σ⁻¹ j) hi
        simpa [Perm.mul_apply] using this
      have hmem : σ⁻¹ i ∉ (CFSG.QuasithinUnique.Ch1.AltSix.epsPerm x0).support := by
        rw [Perm.mem_support, not_not]
        exact hj
      have hfull : (CFSG.QuasithinUnique.Ch1.AltSix.epsPerm x0).support = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hsupp, Fintype.card_fin])
      exact hmem (hfull ▸ Finset.mem_univ _)
    ·
      have hy := hN _ y0_mem_N2
      have hfpf := fpf_of_normalizes_E2 ((β yA : A6) : Perm (Fin 6))
        (by
          have : β yA ^ 3 = 1 := by
            rw [← map_pow, show yA ^ 3 = 1 from Subtype.ext x0_y0_facts.2.2.2.2.2.2.1, map_one]
          exact congrArg Subtype.val this)
        (fun h => x0_y0_facts.2.2.2.2.2.2.2.1 (by
          have h' : β yA = β 1 := by rw [map_one]; exact Subtype.ext h
          exact congrArg Subtype.val (β.injective h')))
        (mem_N2_iff.mp hy)
      obtain ⟨i, hi⟩ := eps_y0_fixed
      apply hfpf (σ i)
      rw [← hσb, CFSG.QuasithinUnique.Ch1.AltSix.autOf_apply,
        CFSG.QuasithinUnique.Ch1.AltSix.phi_true]
      simp [Perm.mul_apply, CFSG.QuasithinUnique.Ch1.AltSix.epsPerm_apply, hi]

theorem conjNormal_injective :
    Function.Injective (MulAut.conjNormal : Perm (Fin 6) →* MulAut A6) := by
  intro σ τ h
  apply CFSG.QuasithinUnique.Ch1.AltSix.conj_inj
  intro a ha
  have := congrArg (fun f : MulAut A6 => ((f ⟨a, mem_alternatingGroup.mpr ha⟩ : A6) :
    Perm (Fin 6))) h
  simpa [MulAut.conjNormal_apply] using this

end CFSG.Quasithin.H13.L32A.C.Alt6
