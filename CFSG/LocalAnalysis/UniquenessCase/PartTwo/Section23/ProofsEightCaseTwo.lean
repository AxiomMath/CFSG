module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLayer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KThinL2Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_of_isSz_bar2 {K : Subgroup G} {a : ℕ} (h : IsSz (Bar2 K) a) :
    ¬ 3 ∣ Nat.card K :=
  fun h3 => CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h
    ((dvd_card_iff_dvd_card_bar2 Nat.prime_three (by norm_num)).mp h3)

theorem thin8_of_isJ1_bar2 {K : Subgroup G} (h : IsJ1 (Bar2 K)) : F08.Thin8 K := by
  intro p hp hp2
  rw [← pRank_bar2_eq_of_odd hp hp2]
  refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
  rw [(kJ1_holds (Bar2 K) h).1]
  exact CFSG.QuasithinUnique.Id2519.not_sq_dvd_J1 hp hp2

theorem ne_three_of_isL2Odd {X : Type} [Group X] {p : ℕ} (h : IsL2Odd X p) : p ≠ 3 := by
  intro h3
  have hadm := h.admissible
  rw [h3] at hadm
  exact CFSG.Open.StatedAPI.not_psl_two_of_statedLieAdmissible_three_one hadm ⟨rfl, rfl⟩

theorem thin8_of_isL2Odd_bar2 {K : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : IsL2Odd (Bar2 K) p) : F08.Thin8 K := by
  intro q hq hq2
  rw [← pRank_bar2_eq_of_odd hq hq2]
  rcases lt_or_ge 5 p with h5 | h5
  · exact kThinL2Odd_holds (Bar2 K) p h5 h q hq hq2
  · have hp3 : p ≠ 3 := ne_three_of_isL2Odd h
    have hp4 : p ≠ 4 := by
      intro h4
      rw [h4] at hp
      norm_num at hp
    have hp5 : p = 5 := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hL2five : IsL2 (Bar2 K) 2 :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_isL2_two_of_isL2Odd_five (hp5 ▸ h)
    exact pRank_le_one_of_isL2_or_isSz (Or.inl hL2five) hq hq2

theorem Ctx23L.isL2_or_isL2Odd_or_isJ1_of_three_dvd_card {D : Data G} {Ch : Choice2011 G}
    (hI : ∀ K' ∈ calC D.M, ∀ a : ℕ, ¬ (Odd a ∧ IsSp4 (Bar2 K') a) ∧ ¬ IsSU3 (Bar2 K') a)
    (h2116 : S21_16 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {K' : Subgroup G}
    (hK' : K' ∈ calC D.M) (h3 : 3 ∣ Nat.card K') :
    (∃ n : ℕ, IsL2 (Bar2 K') n) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 K') p) ∨ IsJ1 (Bar2 K') := by
  rcases h2116 h1930 c.withB0.toCtx23.toCtx21 K' hK' with
    ⟨n, hn, hsp⟩ | ⟨n, hsu⟩ | ⟨n, hL2⟩ | ⟨n, hSz⟩ | ⟨p, hp, hp2, hL2Odd⟩ | hJ1
  · exact absurd ⟨hn, hsp⟩ (hI K' hK' n).1
  · exact absurd hsu (hI K' hK' n).2
  · exact Or.inl ⟨n, hL2⟩
  · exact absurd h3 (not_three_dvd_card_of_isSz_bar2 hSz)
  · exact Or.inr (Or.inl ⟨p, hp, hp2, hL2Odd⟩)
  · exact Or.inr (Or.inr hJ1)

theorem Ctx23L.not_three_dvd_card_of_ne {D : Data G} {Ch : Choice2011 G}
    (hI : ∀ K' ∈ calC D.M, ∀ a : ℕ, ¬ (Odd a ∧ IsSp4 (Bar2 K') a) ∧ ¬ IsSU3 (Bar2 K') a)
    (h2116 : S21_16 D Ch) (h2119 : S21_19 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    (hshape : IsJ1 (Bar2 K) ∨ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ IsL2Odd (Bar2 K) p)
    {K' : Subgroup G} (hK' : K' ∈ calC D.M) (hne : K' ≠ K) : ¬ 3 ∣ Nat.card K' := by
  intro h3
  have h19 := h2119 h1930 c.withB0.toCtx23.toCtx21 K hK K' hK' hne.symm hKn hshape
  rcases Ctx23L.isL2_or_isL2Odd_or_isJ1_of_three_dvd_card hI h2116 h1930 c hK' h3 with
    ⟨n, hL2⟩ | ⟨p, hp, hp2, hL2Odd⟩ | hJ1
  · exact h19 (Or.inl ⟨n, hL2⟩)
  · exact h19 (Or.inr (Or.inr (Or.inr ⟨p, hp, hL2Odd⟩)))
  · exact h19 (Or.inr (Or.inr (Or.inl hJ1)))

private theorem exists_fixed_seven_of_isJ1 {D : Data G} {K : Subgroup G} {b : G}
    (hK : K ∈ calC D.M) (hJ1 : IsJ1 (Bar2 K))
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hborder : orderOf b = 7) :
    ∃ z : BarInf K ⧸ Subgroup.center (BarInf K),
      orderOf z = 7 ∧ inducedQuotInfAut K b hbN z = z := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  haveI : IsSimpleGroup (Bar2 K) := (kJ1_holds (Bar2 K) hJ1).2.1
  have hc : Subgroup.center (Bar2 K) = ⊥ := uc22p21k_center_eq_bot hq
  let e : (BarInf K ⧸ Subgroup.center (BarInf K)) ≃* Bar2 K := quotCenterEquivBar2 hq hc
  let θ := inducedQuotInfAut K b hbN
  obtain ⟨x, hx⟩ := (kJ1_holds (Bar2 K) hJ1).2.2 (MulAut.congr e θ)
  have hθdvd : orderOf θ ∣ 7 := (orderOf_inducedQuotInfAut_dvd K hbN).trans (by rw [hborder])
  have hcongr : orderOf (MulAut.congr e θ) = orderOf θ :=
    orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ
  have h7 : orderOf (MulAut.conj x) ∣ 7 := by
    rw [← hx, hcongr]
    exact hθdvd
  obtain ⟨z, hz7, hzfix⟩ : ∃ z : Bar2 K, orderOf z = 7 ∧ MulAut.conj x z = z := by
    by_cases hx1 : MulAut.conj x = 1
    · haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 K) 7
        (by rw [(kJ1_holds (Bar2 K) hJ1).1]; norm_num)
      exact ⟨z, hz, by simp [hx1]⟩
    · have h7' : orderOf (MulAut.conj x) = 7 := by
        rcases (Nat.dvd_prime Nat.prime_seven).mp h7 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1
        · exact h
      have hdvd : 7 ∣ orderOf x :=
        h7' ▸ orderOf_map_dvd (MulAut.conj : Bar2 K →* MulAut (Bar2 K)) x
      have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
      refine ⟨x ^ (orderOf x / 7), orderOf_pow_orderOf_div hx0 hdvd, ?_⟩
      rw [MulAut.conj_apply]
      group
  refine ⟨e.symm z, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hz7
  · apply e.injective
    have h1 : (MulAut.congr e θ) z = z := by rw [hx]; exact hzfix
    have h2 : e (θ (e.symm z)) = z := h1
    rw [h2, MulEquiv.apply_symm_apply]

private theorem false_of_isJ1_conjSet {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hJ1 : IsJ1 (Bar2 K)) (hn3 : c.withB0.n = 3)
    (huniq : ∀ A : Subgroup G, A ≤ K → Nat.card A = 7 → A ∈ uniqueSet D.M) : False := by
  classical
  have hm3 : CFSG.Open.pRank 2 D.Z = 3 := by
    rcases h52 h1930 c.withB0 with h | ⟨-, -, h⟩
    · exact h.symm.trans hn3
    · omega
  obtain ⟨-, hP1⟩ := c.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930
  obtain ⟨b, hb0, hborder, hbZ⟩ := hP1 7 Nat.prime_seven (by rw [hm3]; norm_num)
  have hbodd : Odd (orderOf b) := hborder ▸ ⟨3, by norm_num⟩
  have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
    c.B0_le_normalizer_of_mem_calC h215 h1930 hK hb0
  obtain ⟨z, hz7, hzfix⟩ := exists_fixed_seven_of_isJ1 hK hJ1 hbN hborder
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  haveI : IsSimpleGroup (Bar2 K) := (kJ1_holds (Bar2 K) hJ1).2.1
  have hc : Subgroup.center (Bar2 K) = ⊥ := uc22p21k_center_eq_bot hq
  have hrZ : ¬ 7 ∣ Nat.card (Subgroup.center (Bar2 K)) := by simp [hc]
  obtain ⟨y, hyC, hyord, -⟩ :=
    exists_mem_centralizer_of_quotInf_fixed hK hbN hbodd Nat.prime_seven (by norm_num) hrZ
      hz7 hzfix
  have hAcard : Nat.card (Subgroup.zpowers (y : G)) = 7 := by
    rw [Nat.card_zpowers, hyord]
  have hAuniq : Subgroup.zpowers (y : G) ∈ uniqueSet D.M :=
    huniq _ (Subgroup.zpowers_le.mpr y.2) hAcard
  have hne : Subgroup.zpowers (y : G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  have hpgrp : IsPGroup 7 ↥(Subgroup.zpowers (y : G)) :=
    IsPGroup.iff_card.mpr ⟨1, by simpa using hAcard⟩
  have hle : Subgroup.zpowers (y : G) ≤ D.M ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf ((Subgroup.zpowers_le.mpr y.2).trans hK.1.le) (Subgroup.zpowers_le.mpr hyC)
  exact ((h54 h1930 c.withB0 b (by simpa using hb0) hbZ).2 7 Nat.prime_seven
    (Subgroup.zpowers (y : G)) hne hpgrp hle).1 hAuniq

theorem Ctx23L.normal_and_barImage_of_isJ1_or_isL2Odd {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h2116 : S21_16 D Ch) (h2117 : S21_17 D Ch)
    (h2119 : S21_19 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hI : ∀ K' ∈ calC D.M, ∀ a : ℕ, ¬ (Odd a ∧ IsSp4 (Bar2 K') a) ∧ ¬ IsSU3 (Bar2 K') a)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hshape : IsJ1 (Bar2 K) ∨ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ IsL2Odd (Bar2 K) p) :
    (K.subgroupOf D.M).Normal ∧ barImage D.M K = Opp 3 (CFSG.layer (Bar2 D.M)) := by
  classical
  have hnorm : (K.subgroupOf D.M).Normal := by
    rcases h2117 h1930 c.withB0.toCtx23.toCtx21 K hK with hconj | hsecond | hthird
    · exact uc22p21j_normal_of_conjClosure_eq hK.1.le hconj
    · obtain ⟨-, n, -, hOr⟩ := hsecond
      rcases hOr with hL2 | hSz
      · rcases hshape with hJ | ⟨p, hp, hp5, hL2Odd⟩
        · exact absurd hL2 (not_isL2_of_isJ1 hJ)
        · exact absurd hL2 (not_isL2_of_isL2Odd hp5 hL2Odd)
      · rcases hshape with hJ | ⟨p, hp, hp5, hL2Odd⟩
        · exact absurd hSz (not_isSz_of_isJ1 hJ)
        · exact absurd hSz (not_isSz_of_isL2Odd (by omega) hL2Odd)
    · obtain ⟨-, hJ1, hn3, -, -, huniq⟩ := hthird
      rcases hshape with hJ | ⟨p, hp, hp5, hL2Odd⟩
      · exact (false_of_isJ1_conjSet hE h207 h52 h53 h54 h215 h1930 c hK hJ1
          (show c.withB0.n = 3 from hn3) huniq).elim
      · exact ((not_isL2Odd_of_isJ1 hp5 hJ1) hL2Odd).elim
  refine ⟨hnorm, ?_⟩
  have hother : ∀ K' ∈ calC D.M, K' ≠ K → ¬ 3 ∣ Nat.card K' := fun K' hK' hne =>
    Ctx23L.not_three_dvd_card_of_ne hI h2116 h2119 h1930 c hK hnorm hshape hK' hne
  have h3 : 3 ∣ Nat.card (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
    have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
    rcases hshape with hJ | ⟨p, hp, hp5, hL2Odd⟩
    · haveI : IsSimpleGroup (Bar2 K) := (kJ1_holds (Bar2 K) hJ).2.1
      have hc : Subgroup.center (Bar2 K) = ⊥ := uc22p21k_center_eq_bot hq
      rw [uc22p21k_card_quot_center hc, (kJ1_holds (Bar2 K) hJ).1]
      norm_num
    · have hc : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isL2Odd hq hL2Odd
      rw [uc22p21k_card_quot_center hc]
      exact three_dvd_card_of_isL2Odd (by omega) hL2Odd
  exact barImage_eq_opp_three_layer hK hother h3

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
