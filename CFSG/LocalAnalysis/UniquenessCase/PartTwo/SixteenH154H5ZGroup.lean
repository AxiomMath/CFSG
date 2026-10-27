module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarDef
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def s16h_ZCondGroup (Y : Type) [Group Y] : Prop :=
  ∀ K T : Subgroup Y, K.Normal → T.Normal → (∀ y ∈ T, ∃ n : ℕ, y ^ 2 ^ n ∈ K) →
    (∃ f : Y, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ f ∉ K ∧ f ^ r ∈ K) → T ≤ K

private theorem s16h_eq_of_ne_one_of_card_le_two {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H ≤ 2) {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcase : Nat.card H = 1 ∨ Nat.card H = 2 := by omega
  rcases hcase with h1 | h2
  · haveI : Subsingleton H := (Finite.card_le_one_iff_subsingleton (α := H)).mp (le_of_eq h1)
    exact absurd (Subsingleton.elim a 1) ha
  · obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
    exact (huniq a ha).trans (huniq b hb).symm

private theorem s16h_perm_fin3_pow_six :
    ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 → σ ^ 3 = 1 ∨ σ ^ 2 = 1 := by
  decide +kernel

private theorem s16h_normal_two_subgroup_perm_fin3_eq_bot {G : Type*} [Group G] [Finite G]
    (ψ : G →* Equiv.Perm (Fin 3)) (hψ : Function.Injective ψ)
    (hodd : ∃ u : G, orderOf u = 3) {T : Subgroup G} [T.Normal]
    (hT2 : ∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n = 1) : T = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hpg : IsPGroup 2 ↥T := fun x => by
    obtain ⟨n, hn⟩ := hT2 x.1 x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hdvd6 : Nat.card ↥T ∣ 6 := by
    have h1 : Nat.card (T.map ψ) ∣ Nat.card (Equiv.Perm (Fin 3)) :=
      Subgroup.card_subgroup_dvd_card (T.map ψ)
    rw [Subgroup.card_map_of_injective hψ, hcard6] at h1
    exact h1
  have hk_le : k ≤ 1 := by
    rw [hk] at hdvd6
    by_contra h
    have h2 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h4 : (4 : ℕ) ∣ 6 := by
      have h1 : (4 : ℕ) ∣ 2 ^ k := by simpa using h2
      exact h1.trans hdvd6
    norm_num at h4
  have hcardT : Nat.card ↥T ∣ 2 := by
    rw [hk]
    exact pow_dvd_pow 2 hk_le
  have hcardTle : Nat.card ↥T ≤ 2 := Nat.le_of_dvd (by norm_num) hcardT
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  by_contra ht1
  obtain ⟨u, hu⟩ := hodd
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  have ht2 : t ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard T ht).trans hcardT)
  have hconj_mem : u * t * u⁻¹ ∈ T := (inferInstance : T.Normal).conj_mem t ht u
  have hcentral : u * t * u⁻¹ = t := by
    have ha : (⟨t, ht⟩ : ↥T) ≠ 1 := fun h1 => ht1 (Subtype.ext_iff.mp h1)
    have hb : (⟨u * t * u⁻¹, hconj_mem⟩ : ↥T) ≠ 1 := by
      intro h1
      apply ha
      have h1' : u * t * u⁻¹ = 1 := Subtype.ext_iff.mp h1
      refine Subtype.ext ?_
      calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
        _ = u⁻¹ * 1 * u := by rw [h1']
        _ = 1 := by group
    exact (Subtype.ext_iff.mp
      (s16h_eq_of_ne_one_of_card_le_two hcardTle ha hb)).symm
  have hu3 : u ^ 3 = 1 := by simpa [hu] using pow_orderOf_eq_one u
  have hu2ne : u ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hu] at hdvd
    norm_num at hdvd
  have htu : t * u = u * t := by
    have h1 : u * t = t * u := by
      calc u * t = (u * t * u⁻¹) * u := by group
        _ = t * u := by rw [hcentral]
    exact h1.symm
  have hψt2 : (ψ t) ^ 2 = 1 := by
    calc (ψ t) ^ 2 = ψ (t ^ 2) := (map_pow ψ t 2).symm
      _ = ψ 1 := by rw [ht2]
      _ = 1 := map_one ψ
  have hψu3 : (ψ u) ^ 3 = 1 := by
    calc (ψ u) ^ 3 = ψ (u ^ 3) := (map_pow ψ u 3).symm
      _ = ψ 1 := by rw [hu3]
      _ = 1 := map_one ψ
  have htu3 : (t * u) ^ 3 = t := by
    rw [Commute.mul_pow htu 3]
    rw [show t ^ 3 = t by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, ht2, one_mul],
      hu3, mul_one]
  have htu6 : (t * u) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, htu3, ht2]
  have hcomm_ψ : Commute (ψ t) (ψ u) := by
    show ψ t * ψ u = ψ u * ψ t
    rw [(map_mul ψ t u).symm, ← map_mul, htu]
  have hσ6 : (ψ t * ψ u) ^ 6 = 1 := by
    calc (ψ t * ψ u) ^ 6 = (ψ (t * u)) ^ 6 := by rw [map_mul]
      _ = ψ ((t * u) ^ 6) := (map_pow ψ (t * u) 6).symm
      _ = ψ 1 := by rw [htu6]
      _ = 1 := map_one ψ
  rcases s16h_perm_fin3_pow_six (ψ t * ψ u) hσ6 with h3 | h2
  · have h3' : (ψ t) ^ 3 = 1 := by
      have h := h3
      rw [hcomm_ψ.mul_pow 3] at h
      rw [hψu3, mul_one] at h
      exact h
    have hψt : ψ t = 1 := by
      calc ψ t = (ψ t) ^ 2 * ψ t := by rw [hψt2, one_mul]
        _ = (ψ t) ^ 3 := (pow_succ (ψ t) 2).symm
        _ = 1 := h3'
    exact ht1 (hψ (by rw [hψt, map_one]))
  · have h2' : (ψ u) ^ 2 = 1 := by
      have h := h2
      rw [hcomm_ψ.mul_pow 2] at h
      rw [hψt2, one_mul] at h
      exact h
    exact hu2ne (hψ (by rw [map_pow, h2', map_one]))

private theorem s16h_zcondGroup_of_odd_card {Y : Type} [Group Y] [Finite Y]
    (hodd : Odd (Nat.card Y)) : s16h_ZCondGroup Y := by
  intro K T hK hT h2 hf
  haveI : K.Normal := hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmapbot : T.map (QuotientGroup.mk' K) = ⊥ := by
    have hpg : IsPGroup 2 (T.map (QuotientGroup.mk' K)) := by
      intro x
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨n, hn⟩ := h2 y hy
      refine ⟨n, Subtype.ext ?_⟩
      change (x : Y ⧸ K) ^ 2 ^ n = 1
      rw [← hyx, ← map_pow]
      exact (QuotientGroup.eq_one_iff (y ^ 2 ^ n)).mpr hn
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvdQ : Nat.card (Y ⧸ K) ∣ Nat.card Y := by
      refine ⟨Nat.card K, ?_⟩
      rw [mul_comm, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
    have hdvd : Nat.card ↥(T.map (QuotientGroup.mk' K)) ∣ Nat.card Y :=
      (Subgroup.card_subgroup_dvd_card _).trans hdvdQ
    have hoddT : Odd (Nat.card ↥(T.map (QuotientGroup.mk' K))) := hodd.of_dvd_nat hdvd
    have hk0 : k = 0 := by
      by_contra hkne
      have h2dvd : 2 ∣ Nat.card ↥(T.map (QuotientGroup.mk' K)) := by
        rw [hk]
        exact dvd_pow_self 2 (by omega)
      exact hoddT.not_two_dvd_nat h2dvd
    have hcard_one : Nat.card ↥(T.map (QuotientGroup.mk' K)) = 1 := by
      rw [hk, hk0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq (T.map (QuotientGroup.mk' K)) hcard_one
  exact ((Subgroup.map_eq_bot_iff T).mp hmapbot).trans (le_of_eq (QuotientGroup.ker_mk' K))

private theorem s16h_zcondGroup_of_simple {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] :
    s16h_ZCondGroup Y := by
  intro K T hK hT h2 hf
  haveI : K.Normal := hK
  haveI : T.Normal := hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hKbot | hKtop
  · subst hKbot
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hTbot | hTtop
    · rw [hTbot]
    · exfalso
      obtain ⟨f, r, hr, hr2, hfK, hfr⟩ := hf
      have hfne : f ≠ 1 := fun h1 => hfK (Subgroup.mem_bot.mpr h1)
      have hfr1 : f ^ r = 1 := Subgroup.mem_bot.mp hfr
      haveI : Fact r.Prime := ⟨hr⟩
      have hord : orderOf f = r := orderOf_eq_prime hfr1 hfne
      have hpgT : IsPGroup 2 T := by
        intro x
        obtain ⟨n, hn⟩ := h2 x.1 x.2
        exact ⟨n, Subtype.ext (Subgroup.mem_bot.mp hn)⟩
      have hpgTop : IsPGroup 2 (⊤ : Subgroup Y) := hTtop ▸ hpgT
      obtain ⟨n, hn⟩ := hpgTop ⟨f, Subgroup.mem_top f⟩
      have hf2n : f ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hdvd : r ∣ 2 ^ n := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one hf2n
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  · rw [hKtop]; exact le_top

private theorem s16h_gl3_card_of_seven_dvd
    (K : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) (h7dvd : 7 ∣ Nat.card ↥K) :
    Nat.card ↥K = 7 ∨ Nat.card ↥K = 21 ∨ K = ⊤ := by
  by_cases h2 : 2 ∣ Nat.card ↥K
  · exact Or.inr (Or.inr
      (CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32 h2 h7dvd))
  · have hdvd168 : Nat.card ↥K ∣ 168 :=
      CFSG.ComponentClassification.GHarris.card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card K
    have hcard : Nat.card ↥K = 7 ∨ Nat.card ↥K = 21 := by
      obtain ⟨m, hm⟩ := h7dvd
      have hm24 : m ∣ 24 := by
        have h : 7 * m ∣ 7 * 24 := by
          have h' := hdvd168
          rw [hm] at h'
          norm_num at h' ⊢
          exact h'
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 7)).mp h
      have hm2 : ¬ 2 ∣ m := fun h2m => h2 (by
        rw [hm]
        exact Dvd.dvd.mul_left h2m 7)
      have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm24 (by norm_num)
      have hmle : m ≤ 24 := Nat.le_of_dvd (by norm_num) hm24
      have hodd : Odd m := by
        rcases Nat.even_or_odd m with he | ho
        · exact absurd he.two_dvd hm2
        · exact ho
      have hm13 : m = 1 ∨ m = 3 := by
        have hmem : m ∈ (24).divisors := Nat.mem_divisors.mpr ⟨hm24, by norm_num⟩
        have hmem' : m ∈ (24).divisors.filter Odd := Finset.mem_filter.mpr ⟨hmem, hodd⟩
        have hlist : (24).divisors.filter Odd = {1, 3} := by decide
        rw [hlist] at hmem'
        simpa using hmem'
      rcases hm13 with h | h
      · simp [hm, h]
      · simp [hm, h]
    rcases hcard with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem s16h_zcondGroup_of_surjective {Y G : Type} [Group Y] [Group G] (φ : Y →* G)
    (hφ : Function.Surjective φ) (h : s16h_ZCondGroup Y) : s16h_ZCondGroup G := by
  intro K T hK hT h2 hf
  have hK' : (K.comap φ).Normal := hK.comap φ
  have hT' : (T.comap φ).Normal := hT.comap φ
  have h2' : ∀ y ∈ T.comap φ, ∃ n : ℕ, y ^ 2 ^ n ∈ K.comap φ := by
    intro y hy
    rw [Subgroup.mem_comap] at hy
    obtain ⟨n, hn⟩ := h2 (φ y) hy
    refine ⟨n, ?_⟩
    rw [Subgroup.mem_comap, map_pow]
    exact hn
  have hf' : ∃ f : Y, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ f ∉ K.comap φ ∧ f ^ r ∈ K.comap φ := by
    obtain ⟨f, r, hr, hr2, hfK, hfr⟩ := hf
    obtain ⟨y, hy⟩ := hφ f
    refine ⟨y, r, hr, hr2, ?_, ?_⟩
    · rw [Subgroup.mem_comap, hy]; exact hfK
    · rw [Subgroup.mem_comap, map_pow, hy]; exact hfr
  have hTK := h (K.comap φ) (T.comap φ) hK' hT' h2' hf'
  intro t ht
  obtain ⟨y, hy⟩ := hφ t
  have hyT : y ∈ T.comap φ := by rw [Subgroup.mem_comap, hy]; exact ht
  have hyK : y ∈ K.comap φ := hTK hyT
  rwa [Subgroup.mem_comap, hy] at hyK

private theorem s16h_zcondGroup_of_mulEquiv {Y G : Type} [Group Y] [Group G] (e : Y ≃* G)
    (h : s16h_ZCondGroup G) : s16h_ZCondGroup Y :=
  s16h_zcondGroup_of_surjective e.symm.toMonoidHom e.symm.surjective h

theorem s16h_zcondGroup_of_embed_perm_three {Y : Type} [Group Y] (ψ : Y →* Equiv.Perm (Fin 3))
    (hψ : Function.Injective ψ) : s16h_ZCondGroup Y := by
  classical
  haveI : Finite Y := Finite.of_injective ψ hψ
  have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hcard_range : Nat.card ↥ψ.range = Nat.card Y := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ, Subgroup.card_top]
  have hcardY_dvd : Nat.card Y ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rw [hcard_range, hcard6] at h
    exact h
  intro K T hK hT h2 hf
  haveI : K.Normal := hK
  let π : Y →* Y ⧸ K := QuotientGroup.mk' K
  obtain ⟨f, r, hr, hr2, hfK, hfr⟩ := hf
  have hπf_ne : π f ≠ 1 := fun h1 => hfK ((QuotientGroup.eq_one_iff f).mp h1)
  have hπf_pow : (π f) ^ r = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (f ^ r)).mpr hfr
  haveI : Fact r.Prime := ⟨hr⟩
  have hord : orderOf (π f) = r := orderOf_eq_prime hπf_pow hπf_ne
  have hdvd_r : r ∣ Nat.card (Y ⧸ K) := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hdvdQ : Nat.card (Y ⧸ K) ∣ Nat.card Y := by
    refine ⟨Nat.card K, ?_⟩
    rw [mul_comm, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
  have hr6 : r ∣ 6 := (hdvd_r.trans hdvdQ).trans hcardY_dvd
  have hr3 : r = 3 := by
    have h6 : r ∣ 2 * 3 := by rwa [show (2 * 3 : ℕ) = 6 by norm_num]
    rcases (Nat.Prime.dvd_mul hr).mp h6 with h2' | h3'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2') hr2
    · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3'
  have h3dvd : 3 ∣ Nat.card (Y ⧸ K) := hr3 ▸ hdvd_r
  by_contra hTK
  have hmap_ne : T.map π ≠ ⊥ := by
    intro hbot
    apply hTK
    intro x hx
    have hx' : π x ∈ T.map π := Subgroup.mem_map_of_mem π hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp hx'
  have hpg : IsPGroup 2 (T.map π) := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨n, hn⟩ := h2 y hy
    refine ⟨n, Subtype.ext ?_⟩
    change (x : Y ⧸ K) ^ 2 ^ n = 1
    rw [← hyx, ← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 2 ^ n)).mpr hn
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hcard_ne_one : Nat.card ↥(T.map π) ≠ 1 := by
    intro h1
    exact hmap_ne (Subgroup.eq_bot_of_card_eq (T.map π) h1)
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    exact hcard_ne_one (by rw [hk, hkzero, pow_zero])
  have h2dvd : 2 ∣ Nat.card (Y ⧸ K) := by
    have h2dvdT : 2 ∣ Nat.card ↥(T.map π) := by
      rw [hk]
      exact dvd_pow_self 2 (by omega)
    exact h2dvdT.trans (Subgroup.card_subgroup_dvd_card (T.map π))
  have h6dvd : 6 ∣ Nat.card (Y ⧸ K) := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2dvd h3dvd
  have hQeq : Nat.card (Y ⧸ K) = 6 := Nat.dvd_antisymm (hdvdQ.trans hcardY_dvd) h6dvd
  have hcardY_eq : Nat.card Y = Nat.card K * Nat.card (Y ⧸ K) := by
    rw [← Subgroup.card_mul_index K, Subgroup.index_eq_card]
  have hcardK : Nat.card K = 1 := by
    have hle : Nat.card K * 6 ≤ 6 := by
      have h1 : Nat.card Y ≤ 6 := Nat.le_of_dvd (by norm_num) hcardY_dvd
      rwa [hcardY_eq, hQeq] at h1
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega
  have hKbot : K = ⊥ := Subgroup.eq_bot_of_card_eq K hcardK
  have hT2 : ∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := h2 x hx
    exact ⟨n, Subgroup.mem_bot.mp (hKbot ▸ hn)⟩
  have hodd : ∃ u : Y, orderOf u = 3 := by
    refine ⟨f, ?_⟩
    have hfK' : f ∉ (⊥ : Subgroup Y) := hKbot ▸ hfK
    have hfne : f ≠ 1 := fun h1 => hfK' (Subgroup.mem_bot.mpr h1)
    have hfr1 : f ^ r = 1 := Subgroup.mem_bot.mp (hKbot ▸ hfr)
    rw [← hr3]
    exact orderOf_eq_prime hfr1 hfne
  have hTbot : T = ⊥ := s16h_normal_two_subgroup_perm_fin3_eq_bot ψ hψ hodd hT2
  exact hTK (hTbot.symm ▸ bot_le)

theorem s16h_zcondGroup_of_embed_gl3 {Y : Type} [Group Y] [Finite Y]
    (ψ : Y →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (hψ : Function.Injective ψ)
    (h7 : 7 ∣ Nat.card Y) : s16h_ZCondGroup Y := by
  classical
  haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := s16t3_gl3_isSimpleGroup
  have hcard_range : Nat.card ↥ψ.range = Nat.card Y := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ, Subgroup.card_top]
  have h7' : 7 ∣ Nat.card ↥ψ.range := by rw [hcard_range]; exact h7
  rcases s16h_gl3_card_of_seven_dvd ψ.range h7' with h7c | h21c | htop
  · refine s16h_zcondGroup_of_odd_card ?_
    rw [← hcard_range, h7c]
    exact ⟨3, by norm_num⟩
  · refine s16h_zcondGroup_of_odd_card ?_
    rw [← hcard_range, h21c]
    exact ⟨10, by norm_num⟩
  · have hsurj : Function.Surjective ψ := fun g => by
      have hg : g ∈ ψ.range := by rw [htop]; exact Subgroup.mem_top g
      exact MonoidHom.mem_range.mp hg
    exact s16h_zcondGroup_of_mulEquiv (MulEquiv.ofBijective ψ ⟨hψ, hsurj⟩)
      s16h_zcondGroup_of_simple

private theorem s16h_le_stabSub_commSub_fixV {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} :
    normalizer (L : Set (MulAut W)) ≤ stabSub (commSub ⊤ L ⊓ fixV L) := by
  intro x hx
  have hxnorm : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hxinvnorm : ∀ l ∈ L, x⁻¹ * l * (x⁻¹)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hx) l).mp hl
  have hxZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxnorm u hu.1, ?_⟩
    intro l hl
    calc l (x u) = x ((x⁻¹ * l * x) u) := by simp [MulAut.mul_apply]
      _ = x u := by rw [mem_fixV.mp hu.2 (x⁻¹ * l * x) (by simpa using hxinvnorm l hl)]
  have hxinvZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x⁻¹ u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxinvnorm u hu.1, ?_⟩
    intro l hl
    calc l (x⁻¹ u) = x⁻¹ ((x * l * x⁻¹) u) := by simp [MulAut.mul_apply]
      _ = x⁻¹ u := by rw [mem_fixV.mp hu.2 (x * l * x⁻¹) (hxnorm l hl)]
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by have := hxinvZ (x u) hu; simpa using this, hxZ u⟩

theorem s16h_H5ZCond_of_autSub {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (h : s16h_ZCondGroup ↥(autSub (A ⊓ normalizer (L : Set (MulAut W)))
      (commSub ⊤ L ⊓ fixV L))) : s16h_H5ZCond A L := by
  classical
  refine Or.inr ?_
  intro T hTN hTnorm hT2 hf
  set N : Subgroup (MulAut W) := A ⊓ normalizer (L : Set (MulAut W)) with hN
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZdef
  have hNZ : N ≤ stabSub Z := by
    rw [hN, hZdef]
    exact inf_le_right.trans s16h_le_stabSub_commSub_fixV
  let g : ↥N →* MulAut Z := (resHom Z).comp (Subgroup.inclusion hNZ)
  have hgrange : g.range = autSub N Z := by
    change ((resHom Z).comp (Subgroup.inclusion hNZ)).range = autSub N Z
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let hcod : ∀ n : ↥N, g n ∈ autSub N Z :=
    fun n => hgrange ▸ (show g n ∈ g.range from ⟨n, rfl⟩)
  let ρ : ↥N →* ↥(autSub N Z) := g.codRestrict (autSub N Z) hcod
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : MulAut Z) ∈ g.range := by
      rw [hgrange]
      exact y.2
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, Subtype.ext hn⟩
  have hker_g : ∀ n : ↥N, g n = 1 ↔ (n : MulAut W) ∈ centSub Z := by
    intro n
    constructor
    · intro hn
      have hmem : (Subgroup.inclusion hNZ n : stabSub Z) ∈ (resHom Z).ker := by
        rw [MonoidHom.mem_ker]
        change g n = 1
        exact hn
      rw [ker_resHom Z, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · intro hn
      have hmem : (Subgroup.inclusion hNZ n : stabSub Z) ∈ (resHom Z).ker := by
        rw [ker_resHom Z, Subgroup.mem_subgroupOf]
        exact hn
      rw [MonoidHom.mem_ker] at hmem
      change g n = 1
      exact hmem
  have hker_ρ : ∀ n : ↥N, ρ n = 1 ↔ (n : MulAut W) ∈ centSub Z := by
    intro n
    have hρn : ρ n = 1 ↔ g n = 1 :=
      ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    rw [hρn, hker_g n]
  set T' : Subgroup ↥(autSub N Z) := (T.subgroupOf N).map ρ with hT'def
  haveI hT'norm : T'.Normal := by
    haveI hTNnorm : (T.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff hTN).mpr (fun h k hh hk => hTnorm k hk h hh)
    rw [hT'def]
    exact hTNnorm.map ρ hρsurj
  have hT'2 : ∀ y ∈ T', ∃ m : ℕ, y ^ 2 ^ m ∈ (⊥ : Subgroup ↥(autSub N Z)) := by
    intro y hy
    rw [hT'def] at hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    have hnT : (n : MulAut W) ∈ T := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨m, hm⟩ := hT2 (n : MulAut W) hnT
    refine ⟨m, ?_⟩
    rw [Subgroup.mem_bot]
    calc (ρ n) ^ 2 ^ m = ρ (n ^ 2 ^ m) := (map_pow ρ n (2 ^ m)).symm
      _ = 1 := by rw [hker_ρ]; simpa using hm
  obtain ⟨f, hfN, q, hq, hq2, hfZ, hfq⟩ := hf
  have hfρ : ρ ⟨f, hfN⟩ ≠ 1 := fun h1 => hfZ ((hker_ρ ⟨f, hfN⟩).mp h1)
  have hfqρ : (ρ ⟨f, hfN⟩) ^ q ∈ (⊥ : Subgroup ↥(autSub N Z)) := by
    rw [Subgroup.mem_bot, ← map_pow, hker_ρ]
    simpa using hfq
  have hT'bot : T' ≤ ⊥ :=
    h ⊥ T' inferInstance hT'norm hT'2
      ⟨ρ ⟨f, hfN⟩, q, hq, hq2, by simpa [Subgroup.mem_bot] using hfρ, hfqρ⟩
  intro x hx
  have hxN : x ∈ N := hTN hx
  have hρx : ρ ⟨x, hxN⟩ = 1 := by
    have hmem : ρ ⟨x, hxN⟩ ∈ T' := by
      rw [hT'def]
      exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hx)
    have hbot := hT'bot hmem
    rwa [Subgroup.mem_bot] at hbot
  exact (hker_ρ ⟨x, hxN⟩).mp hρx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
