module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31b
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs2

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits Equiv

private theorem abs6_no_normal_two {Y : Type*} [Group Y] [Finite Y] (X : Subgroup Y) [X.Normal]
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∀ N : Subgroup ↥(Subgroup.centralizer (X : Set Y)), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hp
  have hCn : (Subgroup.centralizer (X : Set Y)).Normal := inferInstance
  have hsub : N.map (Subgroup.centralizer (X : Set Y)).subtype ≤
      pCoreOf 2 (Subgroup.centralizer (X : Set Y)) :=
    Subgroup.map_mono (le_pCore 2 hN hp)
  have hnorm : (pCoreOf 2 (Subgroup.centralizer (X : Set Y))).Normal := by
    have hT := normalizer_le_normalizer_pCoreOf 2 (Subgroup.centralizer (X : Set Y))
    rw [Subgroup.normalizer_eq_top_iff.2 hCn] at hT
    exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hT)
  have hO : pCoreOf 2 (Subgroup.centralizer (X : Set Y)) = ⊥ :=
    hO2 _ hnorm (pCoreOf_isPGroup 2 _)
  refine eq_bot_iff.2 fun x hx => ?_
  have hxm : (x : Y) ∈ pCoreOf 2 (Subgroup.centralizer (X : Set Y)) :=
    hsub (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  rw [hO, Subgroup.mem_bot] at hxm
  exact Subgroup.mem_bot.2 (Subtype.ext hxm)

private theorem abs6_exists_mem_of_prime_dvd {Y : Type*} [Group Y] [Finite Y] (X : Subgroup Y)
    (hcop : ∀ (y : Y) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ X) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card ↥(Subgroup.centralizer (X : Set Y))) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    ∃ c : Y, c ∈ X ⊓ Subgroup.centralizer (X : Set Y) ∧ orderOf c = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpd
  refine ⟨(c : Y), Subgroup.mem_inf.2 ⟨?_, c.2⟩, ?_⟩
  · have hcop' : Nat.Coprime p 6 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h6
      rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from h6) with h | h
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    have hpow : (c : Y) ^ p = 1 := by
      have h := pow_orderOf_eq_one c
      rw [hc] at h
      simpa using congrArg (fun x : ↥(Subgroup.centralizer (X : Set Y)) => (x : Y)) h
    exact hcop _ p hpow hcop'
  · rw [Subgroup.orderOf_coe, hc]

theorem centralizer_eq_bot_of_three {Y : Type*} [Group Y] [Finite Y] (X : Subgroup Y) [X.Normal]
    (hsimple : IsSimpleGroup ↥X) (hnab : ¬ ∀ a b : ↥X, a * b = b * a)
    (hcop : ∀ (y : Y) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ X)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hrank : ∃ A B : Subgroup Y, A ≤ X ∧ B ≤ X ∧ Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set Y) ∧ A ⊓ B = ⊥)
    (hm3 : ∀ A B C : Subgroup Y, Nat.card A = 3 → Nat.card B = 3 → Nat.card C = 3 →
      A ≤ Subgroup.centralizer (B : Set Y) → A ≤ Subgroup.centralizer (C : Set Y) →
      B ≤ Subgroup.centralizer (C : Set Y) → A ⊓ B = ⊥ → (A ⊔ B) ⊓ C = ⊥ → False) :
    Subgroup.centralizer (X : Set Y) = ⊥ := by
  set C := Subgroup.centralizer (X : Set Y) with hCdef
  have hCn : C.Normal := inferInstance
  have hXC : X ⊓ C = ⊥ :=
    inf_eq_bot_of_commute hsimple hnab fun x hx y hy => Subgroup.mem_centralizer_iff.1 hy x hx
  by_contra hC
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥C → p = 2 ∨ p = 3 := by
    intro p hp hpd
    by_contra hne
    push Not at hne
    obtain ⟨c, hcXC, hc⟩ := abs6_exists_mem_of_prime_dvd X hcop hp hpd hne.1 hne.2
    rw [hXC, Subgroup.mem_bot] at hcXC
    rw [hcXC, orderOf_one] at hc
    exact hp.one_lt.ne hc
  have h3 : 3 ∣ Nat.card ↥C := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card ↥C) with ⟨k, hk⟩ |
        ⟨p, hp, hpd, hpo⟩
    · exact absurd (hO2 C hCn (IsPGroup.of_card hk)) hC
    · rcases hprime p hp hpd with rfl | rfl
      · exact absurd hpo (by decide)
      · exact hpd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hcent : ∀ S : Subgroup Y, S ≤ X →
      S ≤ Subgroup.centralizer (Subgroup.zpowers (c : Y) : Set Y) := by
    intro S hS a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hac : Commute a (c : Y) := Subgroup.mem_centralizer_iff.1 c.2 a (hS ha)
    exact (hac.zpow_right n).symm.eq
  obtain ⟨A, B, hAX, hBX, hA, hB, hAB, hAB0⟩ := hrank
  have hZ : Nat.card (Subgroup.zpowers (c : Y)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc]
  have hZC : Subgroup.zpowers (c : Y) ≤ C := Subgroup.zpowers_le.2 c.2
  have hi' : (A ⊔ B) ⊓ Subgroup.zpowers (c : Y) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf (sup_le hAX hBX) hZC).trans hXC.le)
  exact hm3 A B _ hA hB hZ hAB (hcent A hAX) (hcent B hBX) hAB0 hi'

theorem centralizer_le_of_center_three {Y : Type*} [Group Y] [Finite Y] (X : Subgroup Y)
    [X.Normal] (hZ : Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set Y)) = 3)
    (hcop : ∀ (y : Y) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ X)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (h9 : ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer (X : Set Y))) :
    Subgroup.centralizer (X : Set Y) ≤ X := by
  set C := Subgroup.centralizer (X : Set Y) with hCdef
  have hCn : C.Normal := inferInstance
  have hZC : X ⊓ C ≤ C := inf_le_right
  have hO2C := abs6_no_normal_two X hO2
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥C → p = 2 ∨ p = 3 := by
    intro p hp hpd
    by_contra hne
    push Not at hne
    obtain ⟨c, hcXC, hc⟩ := abs6_exists_mem_of_prime_dvd X hcop hp hpd hne.1 hne.2
    have h1 := orderOf_dvd_natCard (⟨c, hcXC⟩ : ↥(X ⊓ C))
    rw [Subgroup.orderOf_mk, hc, hZ] at h1
    exact hne.2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)
  have hle6 : Nat.card ↥C ≤ 6 := card_le_six_of_primes hprime h9 hO2C
  have h3dvd : 3 ∣ Nat.card ↥C := by
    have := Subgroup.card_dvd_of_le hZC
    rwa [hZ] at this
  have hle3 : 3 ≤ Nat.card ↥C := by
    have := Subgroup.card_le_of_le hZC
    rwa [hZ] at this
  have hcases : Nat.card ↥C = 3 ∨ Nat.card ↥C = 6 := by
    obtain ⟨k, hk⟩ := h3dvd
    omega
  rcases hcases with h3 | h6
  ·
    have heq : X ⊓ C = C := Subgroup.eq_of_le_of_card_ge hZC (by omega)
    exact heq.symm.le.trans inf_le_left
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card ↥C by omega)
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card ↥(X ⊓ C) by omega)
    obtain ⟨t, htC, ht2⟩ : ∃ t : Y, t ∈ C ∧ orderOf t = 2 :=
      ⟨(t₀ : Y), t₀.2, by rw [Subgroup.orderOf_coe, ht₀]⟩
    obtain ⟨z, hzX, hzC, hz3⟩ : ∃ z : Y, z ∈ X ∧ z ∈ C ∧ orderOf z = 3 :=
      ⟨(w : Y), (Subgroup.mem_inf.1 w.2).1, (Subgroup.mem_inf.1 w.2).2,
        by rw [Subgroup.orderOf_coe, hw]⟩
    have hzt : z * t = t * z := Subgroup.mem_centralizer_iff.1 htC z hzX
    set M : Subgroup Y := Subgroup.centralizer ({t} : Set Y) ⊓ C with hM
    have htM : t ∈ M := Subgroup.mem_inf.2
      ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh], htC⟩
    have hzM : z ∈ M := Subgroup.mem_inf.2
      ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hzt.symm, hzC⟩
    have h2M : 2 ∣ Nat.card ↥M := by
      have := orderOf_dvd_natCard (⟨t, htM⟩ : ↥M)
      rwa [Subgroup.orderOf_mk, ht2] at this
    have h3M : 3 ∣ Nat.card ↥M := by
      have := orderOf_dvd_natCard (⟨z, hzM⟩ : ↥M)
      rwa [Subgroup.orderOf_mk, hz3] at this
    have h6M : 6 ∣ Nat.card ↥M := by omega
    have hdvdM : Nat.card ↥M ∣ 6 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : M ≤ C)
      rwa [h6] at this
    have hcardM : Nat.card ↥M = 6 := Nat.dvd_antisymm hdvdM h6M
    have hMC : M = C := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    have hCt : ∀ g ∈ C, t * g = g * t := fun g hg => by
      have hgM : g ∈ M := by rw [hMC]; exact hg
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hgM).1 t (Set.mem_singleton t)
    set t' : ↥C := ⟨t, htC⟩ with ht'
    have hcen : t' ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hCt (g : Y) g.2).symm
    have hnorm : (Subgroup.zpowers t').Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hcen)
    have hp2 : IsPGroup 2 ↥(Subgroup.zpowers t') := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, ht', Subgroup.orderOf_mk, ht2, pow_one]
    have ht'1 : t' = 1 := by
      have := Subgroup.mem_zpowers t'
      rwa [hO2C _ hnorm hp2, Subgroup.mem_bot] at this
    have ht1 : t = 1 := congrArg Subtype.val ht'1
    rw [ht1, orderOf_one] at ht2
    norm_num at ht2

end CFSG.Quasithin.H13.S126P31
