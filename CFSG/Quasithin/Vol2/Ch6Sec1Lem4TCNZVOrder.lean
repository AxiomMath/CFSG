module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch1EightFourCore

public section

namespace CFSG.Quasithin.H13.T614.NZVOrder

open CFSG.Quasithin CFSG.Quasithin.Ch1Four

private theorem prime_dvd_tits_mul_two_pow {p j : ℕ} (hp : p.Prime) (h : p ∣ 17971200 * 2 ^ j) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 13 := by
  have e : 17971200 * 2 ^ j = 2 ^ (11 + j) * 3 ^ 3 * 5 ^ 2 * 13 := by ring
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
        (hp.dvd_of_dvd_pow h2))))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)))

private theorem ne_two_pow_mul_four_pow {j n : ℕ} (hn : 2 ≤ n)
    (hm : 2 ^ n * (4 ^ n - 1) = 17971200 * 2 ^ j) : False := by
  have hdvd : (4 ^ n - 1) ∣ 8775 * 2 ^ (11 + j) := by
    have h1 : 4 ^ n - 1 ∣ 17971200 * 2 ^ j := by
      rw [← hm]
      exact Dvd.intro_left _ rfl
    have e : 17971200 * 2 ^ j = 8775 * 2 ^ (11 + j) := by ring
    rwa [e] at h1
  have h4 : 2 ∣ 4 ^ n := dvd_pow (by norm_num) (by omega)
  have hpos : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hodd : (4 ^ n - 1) % 2 = 1 := by omega
  have hcop : Nat.Coprime (4 ^ n - 1) (2 ^ (11 + j)) := by
    apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
  have hle : 4 ^ n - 1 ≤ 8775 :=
    Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  have hn6 : n ≤ 6 := by
    by_contra hc
    have h7 : 4 ^ 7 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h7
    omega
  have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  interval_cases n <;> norm_num at hm <;> omega

theorem not_initNum_tits (j : ℕ) (NS : ℕ → Prop) : ¬ InitNum (17971200 * 2 ^ j) NS := by
  rintro (⟨c, hc, k, hk⟩ | ⟨n, hn, hm⟩ | h3 | ⟨p, k, n, hp, hp5, hodd, -, hk⟩ |
    ⟨p, k, hp, hp5, -, hk⟩)
  ·
    have h13 : 13 ∣ c := by
      rw [← hk]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by norm_num) _) _
    simp only [finOrders, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at h13
  · exact ne_two_pow_mul_four_pow hn hm.symm
  · exact h3 (Dvd.dvd.mul_right (by norm_num) _)
  ·
    have hS : 17971200 * 2 ^ j * 2 ^ k = 17971200 * 2 ^ (j + k) := by ring
    have hpL : p ∣ 17971200 * 2 ^ (j + k) := by
      rw [← hS, hk]
      exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
    have hS1 : 1 ≤ 2 ^ (j + k) := Nat.one_le_two_pow
    rw [hS] at hk
    rcases prime_dvd_tits_mul_two_pow hp hpL with rfl | rfl | rfl | rfl <;> norm_num at hk <;>
      first
      | omega
      | (obtain ⟨t, rfl⟩ := hodd; omega)
  ·
    have hS : 17971200 * 2 ^ j * 2 ^ k = 17971200 * 2 ^ (j + k) := by ring
    have hpL : p ∣ 17971200 * 2 ^ (j + k) := by
      rw [← hS, hk]
      exact Dvd.dvd.mul_right (dvd_pow_self p (by norm_num)) _
    have hS1 : 1 ≤ 2 ^ (j + k) := Nat.one_le_two_pow
    rw [hS] at hk
    rcases prime_dvd_tits_mul_two_pow hp hpL with rfl | rfl | rfl | rfl <;> norm_num at hk <;>
      omega

theorem card_modO2_of_surj {K Q : Type} [Group K] [Group Q] [Finite K] (ψ : K →* Q)
    (hψ : Function.Surjective ψ) (hN : IsPGroup 2 ψ.ker) :
    ∃ i : ℕ, Nat.card (Q ⧸ CFSG.pCore 2 Q) = Nat.card (K ⧸ CFSG.pCore 2 K) * 2 ^ i := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Q := Finite.of_surjective ψ hψ
  set S : Subgroup Q := CFSG.pCore 2 Q with hS
  set C : Subgroup K := CFSG.pCore 2 K with hC
  set P : Subgroup K := S.comap ψ with hP
  have hSn : S.Normal := CFSG.pCore_normal (p := 2) (G := Q)
  have hCn : C.Normal := CFSG.pCore_normal (p := 2) (G := K)
  have hPn : P.Normal := Subgroup.Normal.comap hSn ψ
  have hPS : P.index = S.index := Subgroup.index_comap_of_surjective S hψ
  have hKN : Nat.card ψ.ker * Nat.card Q = Nat.card K := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rwa [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top] at h
  have hSpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hPcard : Nat.card P = Nat.card ψ.ker * Nat.card S := by
    apply Nat.eq_of_mul_eq_mul_left hSpos
    calc S.index * Nat.card P = P.index * Nat.card P := by rw [hPS]
      _ = Nat.card K := P.index_mul_card
      _ = Nat.card ψ.ker * Nat.card Q := hKN.symm
      _ = Nat.card ψ.ker * (S.index * Nat.card S) := by rw [S.index_mul_card]
      _ = S.index * (Nat.card ψ.ker * Nat.card S) := by ring
  have hPp : IsPGroup 2 P := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hN
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := Q))
    rw [IsPGroup.iff_card, hPcard, ha, hb]
    exact ⟨a + b, by rw [pow_add]⟩
  have hPC : P ≤ C := le_sSup ⟨hPn, hPp⟩
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hPC
  obtain ⟨c, hc⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := K))
  have htdvd : t ∣ 2 ^ c := ⟨Nat.card P, by rw [← hc, ht, mul_comm]⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 htdvd
  refine ⟨i, ?_⟩
  have e1 : Nat.card (K ⧸ C) * Nat.card C = Nat.card K :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup C).symm
  have e2 : Nat.card (Q ⧸ S) * Nat.card S = Nat.card Q :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup S).symm
  have hNpos : 0 < Nat.card ψ.ker * Nat.card S := by
    apply Nat.mul_pos
    · exact Nat.card_pos
    · exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hNpos
  calc (Nat.card ψ.ker * Nat.card S) * Nat.card (Q ⧸ S)
      = Nat.card ψ.ker * (Nat.card (Q ⧸ S) * Nat.card S) := by ring
    _ = Nat.card ψ.ker * Nat.card Q := by rw [e2]
    _ = Nat.card K := hKN
    _ = Nat.card (K ⧸ C) * Nat.card C := e1.symm
    _ = Nat.card (K ⧸ C) * (Nat.card P * 2 ^ i) := by rw [ht, hi]
    _ = Nat.card (K ⧸ C) * (Nat.card ψ.ker * Nat.card S * 2 ^ i) := by rw [hPcard]
    _ = (Nat.card ψ.ker * Nat.card S) * (Nat.card (K ⧸ C) * 2 ^ i) := by ring

theorem exists_modO2_surj_of_le {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hKH : K ≤ H) :
    ∃ ψ : ↥K →* ↥(modO2Image H K), Function.Surjective ψ ∧ IsPGroup 2 ψ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  let φ : ↥K →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hKH)
  have hrange : φ.range = modO2Image H K := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkp : IsPGroup 2 φ.ker := by
    intro x
    have hx : Subgroup.inclusion hKH (x : ↥K) ∈ CFSG.pCore 2 ↥H := by
      have := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
      exact this
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (Subgroup.inclusion hKH (x : ↥K)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (Subgroup.inclusion_injective hKH) (by simpa using h1)
  refine ⟨((MulEquiv.subgroupCongr hrange).toMonoidHom).comp φ.rangeRestrict, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hrange).surjective.comp φ.rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hrange).injective,
      MonoidHom.ker_rangeRestrict]
    exact hkp

end CFSG.Quasithin.H13.T614.NZVOrder
