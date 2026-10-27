module

public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup CFSG.RankThree.PartOne

section General

variable {Hh : Type} [Group Hh] [Finite Hh]

theorem orderOf_mk_pPrimeCore {c : Hh} (hc : orderOf c = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Hh) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    rw [this, map_one]
  · intro h1
    have hcK : c ∈ CFSG.pPrimeCore 3 Hh := (QuotientGroup.eq_one_iff c).mp h1
    have := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 Hh) hcK
    rw [hc] at this
    exact hK this

theorem exists_pow_isPGroup_thirteen (K : Subgroup Hh) [K.Normal] {x : Hh}
    (hx : orderOf (QuotientGroup.mk' K x) = 13) :
    ∃ y ∈ Subgroup.zpowers x, IsPGroup 13 (Subgroup.zpowers y) ∧ y ∉ K := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hdvd : 13 ∣ orderOf x := by
    rw [← hx]
    exact orderOf_map_dvd (QuotientGroup.mk' K) x
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨s, r, hr, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos 13 (by norm_num)
  have hr_dvd : r ∣ orderOf x := ⟨13 ^ s, by rw [hm]; ring⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr (dvd_zero 13)
  refine ⟨x ^ r, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) r, ?_, ?_⟩
  · have hord : orderOf (x ^ r) = 13 ^ s := by
      rw [orderOf_pow_of_dvd hr0 hr_dvd, hm]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)
    refine IsPGroup.of_card (n := s) ?_
    rw [Nat.card_zpowers, hord]
  · intro hyK
    have h1 : QuotientGroup.mk' K (x ^ r) = 1 := (QuotientGroup.eq_one_iff _).mpr hyK
    rw [map_pow] at h1
    have h2 : orderOf (QuotientGroup.mk' K x) ∣ r := orderOf_dvd_of_pow_eq_one h1
    rw [hx] at h2
    exact hr h2

theorem pRank_quotient_le (K : Subgroup Hh) [K.Normal] (hK : ¬ 3 ∣ Nat.card K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Hh ⧸ K)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Hh) := by
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' K).ker := by
    rwa [QuotientGroup.ker_mk']
  have h := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three
    (QuotientGroup.mk' K) hker ⊤
  rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)] at h

theorem mem_of_pow_eq_one_of_not_dvd_index {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q)
    [J.Normal] (hJ : ¬ 3 ∣ J.index) {x : Q} (hx : x ^ 3 = 1) : x ∈ J := by
  have h1 : (QuotientGroup.mk x : Q ⧸ J) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hx]
    rfl
  have h2 : orderOf (QuotientGroup.mk x : Q ⧸ J) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk x : Q ⧸ J) ∣ J.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime 3 J.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hJ
  have h4 : orderOf (QuotientGroup.mk x : Q ⧸ J) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

theorem relIndex_eq_card_map (K V : Subgroup Hh) [K.Normal] :
    K.relIndex V = Nat.card (V.map (QuotientGroup.mk' K)) := by
  have h1 := Subgroup.index_ker ((QuotientGroup.mk' K).domRestrict V)
  have hker : ((QuotientGroup.mk' K).domRestrict V).ker = K.subgroupOf V := by
    ext v
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : ((QuotientGroup.mk' K).domRestrict V).range = V.map (QuotientGroup.mk' K) := by
    ext y
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  rw [hker, hrange] at h1
  exact h1

theorem exists_lift_normalizer_zpowers {H₀ : Subgroup Hh} (hH₀ : IsStronglyPEmbedded 3 H₀)
    {c : Hh} (hcH : c ∈ H₀) (hc3 : orderOf c = 3) {n : Hh ⧸ CFSG.pPrimeCore 3 Hh}
    (hn : n ∈ normalizer ((Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) :
      Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh)) : Set (Hh ⧸ CFSG.pPrimeCore 3 Hh))) :
    ∃ h : Hh, h ∈ H₀ ∧ h ∈ normalizer ((Subgroup.zpowers c : Subgroup Hh) : Set Hh) ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) h = n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Hh) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hE : IsPGroup 3 (Subgroup.zpowers c) := StrongP.isPGroup_zpowers_of_pow_eq_one hc3'
  have hne : Subgroup.zpowers c ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    rw [h, orderOf_one] at hc3
    omega
  have hN : normalizer (Subgroup.zpowers c : Set Hh) ≤ H₀ :=
    hH₀.normalizer_le hne hE (Subgroup.zpowers_le.mpr hcH)
  have hmap : (Subgroup.zpowers c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) =
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) :=
    MonoidHom.map_zpowers _ _
  have hn' : n ∈ normalizer (((Subgroup.zpowers c).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) : Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh)) :
      Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
    rw [hmap]
    exact hn
  obtain ⟨h, hh, rfl⟩ := CFSG.LocalAnalysis.GLTheoremB.normalizer_map_quotient_le
    (CFSG.pPrimeCore 3 Hh) hK hE hn'
  exact ⟨h, hN hh, hh, rfl⟩

end General

theorem exists_simple_normal_of_stronglyPEmbedded {Q : Type} [Group Q] [Finite Q]
    (Y : Subgroup Q) (hO : CFSG.pPrimeCore 3 Q = ⊥) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Q) ≤ 1)
    (hY : IsStronglyPEmbedded 3 Y) :
    ∃ J : Subgroup Q, J.Normal ∧ IsSimpleGroup ↥J ∧ (∃ a b : ↥J, a * b ≠ b * a) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 1 ∧ centralizer (J : Set Q) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hs, hnab, hn, hc⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hY
  have h3 : 3 ∣ Nat.card (CFSG.generalizedFitting Q) := by
    by_contra h
    have hle : CFSG.generalizedFitting Q ≤ CFSG.pPrimeCore 3 Q :=
      le_sSup ⟨hn, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h⟩
    rw [hO] at hle
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle a.2))
    rw [ha]
    simp
  obtain ⟨c, hc3⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.generalizedFitting Q) 3 h3
  have hEea : IsElemAbelian 3 (Subgroup.zpowers c) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have hxord : orderOf x ∣ orderOf c := orderOf_dvd_of_mem_zpowers hx
    rw [hc3] at hxord
    exact orderOf_dvd_iff_pow_eq_one.mp hxord
  have hcard : Nat.card (Subgroup.zpowers c) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hc3, pow_one]
  have hge : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.generalizedFitting Q)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hEea hcard
  have hle1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.generalizedFitting Q)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hr
  exact ⟨CFSG.generalizedFitting Q, hn, hs, hnab, le_antisymm hle1 hge, hc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
