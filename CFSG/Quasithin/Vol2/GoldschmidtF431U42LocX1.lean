module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocTp

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem mem_zpowers_two {G : Type*} [Group G] {t c : G} (ht : t * t = 1)
    (hc : c ∈ Subgroup.zpowers t) : c = 1 ∨ c = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  have h : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rw [h]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h0]
    simp
  · right
    rw [h1]
    simp

theorem sY_mem_P2 {p : Fin 45} (hp : p ∈ L0S) : sY p ∈ P2 :=
  B0_le_P2 (T_le_B0 (Vsub_le_T (sY_mem_Vsub hp)))

theorem card_zpowers_tPrime :
    Nat.card (Subgroup.zpowers tPrime) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_two_of_sq tPrime_sq tPrime_ne_one]

theorem sq_fix_of_perm {k : Y} (h0 : (k : P45) 0 = 0)
    (h20 : (k : P45) 20 = 20) (h24 : (k : P45) 24 = 24)
    (h15 : (k : P45) 15 = 15 ∨ (k : P45) 15 = 16) (h16 : (k : P45) 16 = 16 ∨ (k : P45) 16 = 15) :
    ∀ p : Fin 45, p ∈ L0S → ((k * k : Y) : P45) p = p := by
  intro p hp
  have hmul : ∀ q : Fin 45, ((k * k : Y) : P45) q = (k : P45) ((k : P45) q) := fun q => rfl
  rw [hmul]
  rcases (mem_L0S_iff p).1 hp with rfl | rfl | rfl | rfl | rfl
  · rw [h0, h0]
  · rcases h15 with h | h
    · rw [h, h]
    · rcases h16 with h' | h'
      · exact absurd ((k : P45).injective (h.trans h'.symm)) (by decide)
      · rw [h, h']
  · rcases h16 with h | h
    · rw [h, h]
    · rcases h15 with h' | h'
      · exact absurd ((k : P45).injective (h.trans h'.symm)) (by decide)
      · rw [h, h']
  · rw [h20, h20]
  · rw [h24, h24]

theorem eq_zpowers_of_normal
    (K : Subgroup Y) (hKP : K ≤ P2) (hKc : ∀ k ∈ K, k * tPrime = tPrime * k)
    (hKn : ∀ e : Y, e ∈ P2 → e * tPrime = tPrime * e → ∀ k ∈ K, e * k * e⁻¹ ∈ K)
    (hN : tPrime ∈ K) (h4 : ¬ 4 ∣ Nat.card K) : K = Subgroup.zpowers tPrime := by
  have hzK : Subgroup.zpowers tPrime ≤ K := (Subgroup.zpowers_le).2 hN
  have hzV : Subgroup.zpowers tPrime ≤ Vsub := (Subgroup.zpowers_le).2 tPrime_mem_Vsub
  have hsmall : ∀ A : Subgroup Y, A ≤ K → IsPGroup 2 A → Nat.card A ≤ 2 := by
    intro A hAK hAp
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    have hd : Nat.card A ∣ Nat.card K := Subgroup.card_dvd_of_le hAK
    rw [hn] at hd ⊢
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num
    · exact absurd (by simpa using dvd_trans (pow_dvd_pow 2 h) hd) h4
  have hKV : K ⊓ Vsub = Subgroup.zpowers tPrime := by
    have hp : IsPGroup 2 ↥(K ⊓ Vsub) := Vsub_isPGroup.to_le inf_le_right
    have hle := hsmall (K ⊓ Vsub) inf_le_left hp
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hzK hzV)
      (by rw [card_zpowers_tPrime]; exact hle)).symm
  refine le_antisymm (fun k hk => ?_) hzK
  have hkP : k ∈ P2 := hKP hk
  have hkc := hKc k hk
  have hcases : ∀ p : Fin 45, p ∈ L0S →
      sY ((k : P45) p) = sY p ∨ sY ((k : P45) p) = tPrime * sY p := by
    intro p hp
    have hsP : sY p ∈ P2 := sY_mem_P2 hp
    have hsc : sY p * tPrime = tPrime * sY p := Vsub_comm (sY_mem_Vsub hp) tPrime_mem_Vsub
    have h1 : k * sY p * k⁻¹ * (sY p)⁻¹ ∈ K := by
      have : k * (sY p * k⁻¹ * (sY p)⁻¹) = k * sY p * k⁻¹ * (sY p)⁻¹ := by group
      rw [← this]
      exact K.mul_mem hk (hKn (sY p) hsP hsc k⁻¹ (K.inv_mem hk))
    have h2 : k * sY p * k⁻¹ * (sY p)⁻¹ ∈ Vsub :=
      Vsub.mul_mem (P2_conj_V hkP (sY_mem_Vsub hp)) (Vsub.inv_mem (sY_mem_Vsub hp))
    have h3 : k * sY p * k⁻¹ * (sY p)⁻¹ ∈ Subgroup.zpowers tPrime := by
      rw [← hKV]
      exact ⟨h1, h2⟩
    rw [sY_conj] at h3
    rcases mem_zpowers_two tPrime_sq h3 with h | h
    · left
      calc sY ((k : P45) p) = sY ((k : P45) p) * (sY p)⁻¹ * sY p := by group
        _ = sY p := by rw [h]; group
    · right
      calc sY ((k : P45) p) = sY ((k : P45) p) * (sY p)⁻¹ * sY p := by group
        _ = tPrime * sY p := by rw [h]
  have hfix : ∀ p : Fin 45, (p = 0 ∨ p = 20 ∨ p = 24) → p ∈ L0S → (k : P45) p = p := by
    intro p hp hpL
    rcases hcases p hpL with h | h
    · exact sY_inj h
    · exfalso
      have hsc : tPrime * sY p = sY p * tPrime :=
        (Vsub_comm (sY_mem_Vsub hpL) tPrime_mem_Vsub).symm
      rw [hsc] at h
      exact not_isConj_sY_mul hp (h ▸ isConj_xY_sY ((k : P45) p))
  have h0 := hfix 0 (by simp) zero_mem_L0S
  have h20 := hfix 20 (by simp) ((mem_L0S_iff 20).2 (by simp))
  have h24 := hfix 24 (by simp) ((mem_L0S_iff 24).2 (by simp))
  have h15 : (k : P45) 15 = 15 ∨ (k : P45) 15 = 16 := by
    rcases hcases 15 mem_L0S_fifteen with h | h
    · exact Or.inl (sY_inj h)
    · right
      have e : tPrime * sY 15 = sY 16 := by
        rw [← Vsub_comm (sY_mem_Vsub mem_L0S_fifteen) tPrime_mem_Vsub]
        exact sY15_mul_tPrime
      rw [e] at h
      exact sY_inj h
  have h16 : (k : P45) 16 = 16 ∨ (k : P45) 16 = 15 := by
    rcases hcases 16 mem_L0S_sixteen with h | h
    · exact Or.inl (sY_inj h)
    · right
      have e : tPrime * sY 16 = sY 15 := by
        rw [← Vsub_comm (sY_mem_Vsub mem_L0S_sixteen) tPrime_mem_Vsub]
        exact sY16_mul_tPrime
      rw [e] at h
      exact sY_inj h
  have hkk : k * k ∈ Vsub := fix_mem_Vsub (sq_fix_of_perm h0 h20 h24 h15 h16)
  have hkkz : k * k ∈ Subgroup.zpowers tPrime := by
    rw [← hKV]
    exact ⟨K.mul_mem hk hk, hkk⟩
  have hk4 : k ^ 4 = 1 := by
    have : k ^ 4 = (k * k) * (k * k) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    rcases mem_zpowers_two tPrime_sq hkkz with h | h
    · rw [h]
      simp
    · rw [h]
      exact tPrime_sq
  have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
    have hdvd : orderOf k ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one hk4
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hzp : IsPGroup 2 (Subgroup.zpowers tPrime) :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_tPrime]; norm_num)
  have hkcen : k ∈ Subgroup.centralizer ((Subgroup.zpowers tPrime : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hc : Commute k tPrime := hkc
    exact (Commute.zpow_left hc.symm n).eq
  have hknorm : Subgroup.zpowers k ≤
      Subgroup.normalizer ((Subgroup.zpowers tPrime : Subgroup Y) : Set Y) :=
    (Subgroup.zpowers_le).2
      (Subgroup.centralizer_le_normalizer ((Subgroup.zpowers tPrime : Subgroup Y) : Set Y) hkcen)
  have hA : IsPGroup 2 ↥(Subgroup.zpowers tPrime ⊔ Subgroup.zpowers k) :=
    hzp.to_sup_of_normal_left' hkp hknorm
  have hAK : Subgroup.zpowers tPrime ⊔ Subgroup.zpowers k ≤ K :=
    sup_le hzK ((Subgroup.zpowers_le).2 hk)
  have hAeq : Subgroup.zpowers tPrime = Subgroup.zpowers tPrime ⊔ Subgroup.zpowers k :=
    Subgroup.eq_of_le_of_card_ge le_sup_left
      (by rw [card_zpowers_tPrime]; exact hsmall _ hAK hA)
  rw [hAeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)

end CFSG.Quasithin.H13.F431.U42
