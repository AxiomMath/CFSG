module

public import CFSG.Quasithin.Background.E6EightBorel
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

theorem benderType_of_rank_one {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 k ∨
      CFSG.Blueprint.SuzukiModel X 2 k ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 k) :
    ∃ i e : ℕ, BenderType X k i e ∧ (e = 1 ∨ e = (2 ^ k + 1) / Nat.gcd 3 (2 ^ k + 1)) := by
  rcases h with hL | hS | hU
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psl2_of_stated hL
    exact ⟨1, 1, .linear k hk e, Or.inl rfl⟩
  · obtain ⟨a, ha, rfl, ⟨e⟩⟩ :=
      CFSG.ComponentClassification.GMS78.exists_mulEquiv_sz_of_suzukiModel hS
    exact ⟨2, 1, .suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)),
      Or.inl rfl⟩
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hk hU
    have hmodel : CFSG.Theory.Comparator.PSU3Model k = CFSG.Open.PSU3 2 k :=
        CFSG.Models.benderPSU3Model_eq_psu3 k
    exact ⟨3, _, .unitary k hk (e.trans (MulEquiv.subgroupCongr hmodel.symm)), Or.inr rfl⟩

theorem card_comap_of_surjective {G G' : Type*} [Group G] [Group G'] [Finite G] {f : G →* G'}
    (hf : Function.Surjective f) (H : Subgroup G') :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  have : Finite G' := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (H.comap f)
  rw [Subgroup.index_comap_of_surjective H hf] at h1
  have h2 := Subgroup.card_mul_index H
  have h3 : Nat.card G = Nat.card G' * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hpos : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rw [← h2] at h3
  rw [h3] at h1
  have : Nat.card (H.comap f) * H.index = (Nat.card H * Nat.card f.ker) * H.index := by
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem e68BorelKernel_holds : E6.E68BorelKernel := by
  intro L _ _ n hn hL hZ S hS p hp hpn
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hp2 : ¬ p ∣ 2 := by
    intro h
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
    subst hp2
    have : (2 ^ n - 1) % 2 = 1 := by
      have h2n : 2 ^ n % 2 = 0 := Nat.pow_mod 2 n 2 ▸ by simp [Nat.zero_pow (by omega : 0 < n)]
      omega
    omega
  have hpow : ∀ m : ℕ, ¬ p ∣ 2 ^ m := fun m h => hp2 (hp.dvd_of_dvd_pow h)
  set Z := Subgroup.center L with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : Finite (L ⧸ Z) := Finite.of_surjective π hπ
  obtain ⟨i, e, hB, he⟩ := benderType_of_rank_one hn
    (by rcases hL with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))
  have hSodd : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h
  have hZS : Z ≤ S := by
    have h := IsPGroup.le_sylow_of_normal hZ (hS.2.1.toSylow hSodd)
    rwa [IsPGroup.toSylow_coe] at h
  have hcomap : (S.map π).comap π = S := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hZS]
  have hidx : (S.map π).index = S.index := by
    rw [← Subgroup.index_comap_of_surjective (S.map π) hπ, hcomap]
  obtain ⟨t, hc⟩ := hB.exists_benderCore ((hS.2.1.map π).toSylow (by rwa [hidx]))
  have hborel := hc.card_borel
  rw [CFSG.GH74.Uniqueness.Bender.borel, IsPGroup.toSylow_coe] at hborel
  have hN : Subgroup.normalizer (S : Set L) =
      (Subgroup.normalizer ((S.map π : Subgroup (L ⧸ Z)) : Set (L ⧸ Z))).comap π := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hπ, hcomap]
  have hcard := card_comap_of_surjective hπ
    (Subgroup.normalizer ((S.map π : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)))
  rw [← hN, hborel, QuotientGroup.ker_mk'] at hcard
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ
  rw [hcard, hk]
  have hq1 : 2 ^ n - 1 ≠ 0 := by omega
  have he0 : e ≠ 0 := by
    rcases he with rfl | rfl
    · exact one_ne_zero
    · apply Nat.div_ne_zero_iff_of_dvd (Nat.gcd_dvd_right 3 (2 ^ n + 1)) |>.2
      exact ⟨by omega, Nat.gcd_pos_of_pos_left _ (by norm_num) |>.ne'⟩
  have hpe : ¬ p ∣ e := by
    rcases he with rfl | rfl
    · exact hp.not_dvd_one
    · intro hpe
      have hpq : p ∣ 2 ^ n + 1 := hpe.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 _))
      have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq hpn
      have h2' : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
      exact hp2 (h2' ▸ h2)
  rw [← pow_mul, padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity)
    (mul_ne_zero hq1 he0), padicValNat.mul hq1 he0, padicValNat.eq_zero_of_not_dvd (hpow (n * i)),
    padicValNat.eq_zero_of_not_dvd hpe, padicValNat.eq_zero_of_not_dvd (hpow k)]
  ring

end CFSG.Quasithin.H13.NQCat
