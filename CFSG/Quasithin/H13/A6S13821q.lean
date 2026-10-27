module

public import CFSG.Quasithin.H13.A6S13821e
public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.EmptyFaithful.S146F3

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_isPSL_kst_of_hat (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hhat : IsHatA6 L) : ¬ IsPSL 3 2 1 ↥(S.KSt H H) := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := (hS.hF H hH).toHypF91
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  set φ := S1549C.starHom hF with hφ
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hφ, S.ker_starHom_eq hF]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨e⟩ := isPSL_three_two_iff.mp hP
  have hcard : Nat.card ↥(S.KSt H H) = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact SL3.card_S
  have h2 : 2 ≤ CFSG.Open.pRank 3 (S.L1.subgroupOf H) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (S.L1.subgroupOf H),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (Subgroup.subgroupOfEquivOfLe hL1H),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup S.L1]
    exact S.two_le_pRank_L1_of_hat hhat
  have h3 := A6L76F.pRank_le_map_of_not_dvd φ hker (S.L1.subgroupOf H)
  have hle : (S.L1.subgroupOf H).map φ ≤ S.KSt H H := by
    rw [S.kst_top hF]
    exact Subgroup.map_le_range _ _
  have h1 : CFSG.Open.pRank 3 ((S.L1.subgroupOf H).map φ) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEX hE => ?_
    have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 _ g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hdvd : 3 ^ k ∣ 168 := by
      rw [← hk, ← hcard]
      exact Subgroup.card_dvd_of_le (hEX.trans hle)
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      have h9 : 3 ^ 2 ∣ 168 := (pow_dvd_pow 3 h).trans hdvd
      norm_num at h9
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk1
  omega

end Setting4

end CFSG.Quasithin.H13.A6
