module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixAInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_nine_dvd_card_of_not_nine_dvd_card_bar2_19_4 {L : Subgroup G}
    (h : ¬ 9 ∣ Nat.card (Bar2 L)) : ¬ 9 ∣ Nat.card L := by
  intro h9
  have hcard : Nat.card ↥L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcard] at h9
  have hpc : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hpc.exists_card_eq
  rw [hk] at h9
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact h (hcop.dvd_of_dvd_mul_right h9)

theorem card_eq_three_of_isSylowIn_three_19_4 {Q Y L : Subgroup G}
    (hQ : IsSylowIn 3 Q Y) (hQL : Q ≤ L) (hnot9 : ¬ 9 ∣ Nat.card L)
    (h3Y : 3 ∣ Nat.card Y) : Nat.card Q = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Q = 3 ^ (Nat.card Y).factorization 3 :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr hQ).card_eq
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hpos : 0 < (Nat.card Y).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos.ne') h3Y
    have hgt : 1 < 3 ^ (Nat.card Y).factorization 3 :=
      Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hpos) (by norm_num)
    have h1 : Nat.card Q = 1 := by rw [hbot]; simp
    rw [hcard] at h1
    omega
  obtain ⟨b, hb⟩ := hQ.isPGroup.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card L := Subgroup.card_dvd_of_le hQL
  have hb2 : b ≤ 1 := by
    by_contra hle
    have hge : 2 ≤ b := by omega
    apply hnot9
    rw [hb] at hdvd
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
    refine (show 9 ∣ 3 ^ (c + 2) from ?_).trans hdvd
    exact ⟨3 ^ c, by rw [pow_add]; norm_num; ring⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hb
    exact hQne (Subgroup.card_eq_one.mp hb)
  rw [hb, show b = 1 by omega, pow_one]

theorem calP19_4_subset_calPMTA (D : Data G)
    (h8107 : F08.R8107 D) (hsp : IsStronglyPEmbedded 5 D.M) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {J A : Subgroup G}
    (hJ : JChoice19 D L K J) : calP19_4 D L K J A ⊆ calPMTA V₀ D.T A := by
  intro Y hY
  obtain ⟨hYE, q, hqprime, hq2, hqfac, hqcase⟩ := hY
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV : InCalV D.M V₀ := S17.hyp125_inCalV h.hyp.hyp125 hne
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTsyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hJM : J ≤ D.M := by
    rcases hJ with ⟨rfl | rfl, -⟩ | ⟨rfl, -⟩
    · exact hLM
    · exact hKM
    · exact sup_le hLM hKM
  have hJTM : J ⊔ D.T ≤ D.M := sup_le hJM hTM
  have hYM : Y ≤ D.M := hYE.1.trans hJTM
  have hcore_le : pCoreOf 2 D.M ≤ pCoreOf 2 (J ⊔ D.T) := by
    have hO2le : pCoreOf 2 D.M ≤ J ⊔ D.T :=
      (E1.pCoreOf_two_le_of_isSylowIn hTsyl).trans (le_sup_right)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2le ?_ ?_
    · exact hJTM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hE' : E1.IsE 1 D.M D.T A Y := by
    refine ⟨hYM, ?_, hYE.2.2.1, hYE.2.2.2⟩
    have htau : E1.tauOf D.M D.T A ≤ E1.tauOf (J ⊔ D.T) D.T A := by
      intro t ht
      rw [E1.mem_tauOf_of_le hTM] at ht
      rw [E1.mem_tauOf_of_le (le_sup_right : D.T ≤ J ⊔ D.T)]
      exact ⟨ht.1, fun a ha => hcore_le (ht.2 a ha)⟩
    exact htau.trans hYE.2.1
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf q Y
  have hQY : Q ≤ Y := hQ.le
  have hQM : Q ≤ D.M := hQY.trans hYM
  have hn0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hcardY : Nat.card Y =
      2 ^ (Nat.card Y).factorization 2 * q ^ (Nat.card Y).factorization q := by
    have hsupp : (Nat.card Y).factorization.support ⊆ ({2, q} : Finset ℕ) := by
      rw [Nat.support_factorization, hqfac]
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    rw [Finsupp.prod_of_support_subset _ hsupp (fun r e => r ^ e)
      (by intro r hr; simp)]
    rw [Finset.prod_insert (by simp [Ne.symm hq2]), Finset.prod_singleton]
  have hcardT : Nat.card ↥(D.T ⊓ Y) = 2 ^ (Nat.card Y).factorization 2 :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr hYE.2.2.1).card_eq
  have hcardQ : Nat.card Q = q ^ (Nat.card Y).factorization q := hQ.card_eq
  have hdisj : (D.T ⊓ Y) ⊓ Q = ⊥ := by
    rw [eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hxne : (⟨x, hx⟩ : ↥((D.T ⊓ Y) ⊓ Q)) ≠ 1 := by
      intro h1
      exact hx1 (congrArg Subtype.val h1)
    have h2p : IsPGroup 2 ↥((D.T ⊓ Y) ⊓ Q) := hYE.2.2.1.isPGroup.to_inf_left
    have hqp : IsPGroup q ↥((D.T ⊓ Y) ⊓ Q) := hQ.isPGroup.to_inf_right
    have h2d : 2 ∣ orderOf x := by
      simpa [Subgroup.orderOf_coe] using h2p.dvd_orderOf hxne
    have hqd : q ∣ orderOf x := by
      simpa [Subgroup.orderOf_coe] using hqp.dvd_orderOf hxne
    obtain ⟨k, hk⟩ := h2p.exists_card_eq
    have hdvd : orderOf x ∣ Nat.card ↥((D.T ⊓ Y) ⊓ Q) :=
      Subgroup.orderOf_dvd_natCard _ hx
    rw [hk] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp
      (hqprime.dvd_of_dvd_pow (hqd.trans hdvd)))
  have hcardAB : Nat.card ↥(((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G)) =
      Nat.card ↥(D.T ⊓ Y) * Nat.card Q := by
    let f : ↥(D.T ⊓ Y) × ↥Q →
        ↥(((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G)) :=
      fun s => ⟨(s.1 : G) * (s.2 : G), ⟨s.1, s.1.2, s.2, s.2.2, rfl⟩⟩
    have hf : Function.Injective f := by
      intro s t hst
      have h1 : (s.1 : G) * s.2 = (t.1 : G) * t.2 := congrArg Subtype.val hst
      exact Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj) h1
    have h1 : Nat.card (↥(D.T ⊓ Y) × ↥Q) ≤
        Nat.card ↥(((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G)) :=
      Nat.card_le_card_of_injective f hf
    have h2 : Nat.card ↥(((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G)) ≤
        Nat.card ↥(D.T ⊓ Y) * Nat.card Q := Set.natCard_mul_le
    rw [Nat.card_prod] at h1
    exact le_antisymm h2 h1
  have hprodCard : Nat.card ↥(((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G)) =
      Nat.card Y := by
    rw [hcardAB, hcardT, hcardQ]
    exact hcardY.symm
  have hsubset : (((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G)) ⊆ (Y : Set G) := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact Y.mul_mem ha.2 (hQY hb)
  have hYeq : (Y : Set G) = ((D.T ⊓ Y : Subgroup G) : Set G) * (Q : Set G) := by
    refine (Set.eq_of_subset_of_ncard_le hsubset ?_).symm
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hprodCard.symm.le
  have hrankL : CFSG.Open.pRank 3 L = 1 := by
    rcases h.shape with hL2 | hU3
    · exact S17.pRank_three_eq_one_of_isL2 hL2
    · exact S17.pRank_three_eq_one_of_isU3FourPow hU3 ⟨1, by norm_num⟩ (by norm_num)
  have hrankK : CFSG.Open.pRank 3 K = 1 :=
    S17.pRank_three_eq_one_of_isL2 (S17.isL2_PSL2_two_of_isAlt_five h.hKshape)
  have hthinL : F08.Thin8 L ∨ ∃ n : ℕ, IsU3 (Bar2 L) n := by
    rcases h.shape with hL2 | hU3
    · exact Or.inl (S17.thin8_of_isL2 hL2)
    · exact Or.inr ⟨2, hU3⟩
  have hthinK : F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n :=
    Or.inl (S17.thin8_of_isAlt_five h.hKshape)
  have h3L : 3 ∣ Nat.card L := by
    have hbar := three_dvd_bar2_of_shape h.shape
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
    exact hbar.mul_right _
  have h3K : 3 ∣ Nat.card K := by
    have hbar := three_dvd_bar2_of_isAlt h.hKshape
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    exact hbar.mul_right _
  obtain ⟨a₁, ha₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  obtain ⟨a₂, ha₂⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  let A₁ : Subgroup G := Subgroup.zpowers (a₁ : G)
  let A₂ : Subgroup G := Subgroup.zpowers (a₂ : G)
  have hA₁L : A₁ ≤ L := Subgroup.zpowers_le.mpr a₁.2
  have hA₂K : A₂ ≤ K := Subgroup.zpowers_le.mpr a₂.2
  have hA₁card : Nat.card A₁ = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha₁]
  have hA₂card : Nat.card A₂ = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha₂]
  have hpair := h8107 L h.hyp.hL.1 K h.hK (Ne.symm h.hne) hrankL hrankK hthinL hthinK
  have hnot9L : ¬ 9 ∣ Nat.card L :=
    not_nine_dvd_card_of_not_nine_dvd_card_bar2_19_4 (by
      rcases h.shape with hL2 | hU3
      · rw [card_bar2_of_isAlt_five (S17.isAlt_five_of_isL2_two hL2)]
        norm_num
      · have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two
            (CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide))).2.1 rfl
        rw [h1]
        norm_num [CFSG.Open.ordTwistedA]
        rw [show (∏ x ∈ Finset.Icc 2 3, ((4 : ℤ) ^ x - (-1 : ℤ) ^ x).toNat) = 975 by
          norm_num [Finset.prod_Icc_succ_top]]
        norm_num)
  have hnot9K : ¬ 9 ∣ Nat.card K :=
    not_nine_dvd_card_of_not_nine_dvd_card_bar2_19_4 (by
      rw [card_bar2_of_isAlt_five h.hKshape]
      norm_num)
  have hcalP : Q ∈ calP V₀ := by
    rcases hqcase with hq5 | ⟨hq3, hOpp⟩
    · subst q
      refine ⟨5, Nat.prime_five, by norm_num, hQ.isPGroup, ?_, ?_, ?_⟩
      · rw [hN]
        exact hQM
      · rw [hN]
        exact hsp.rankThreeGamma_one_le_of_le Nat.prime_five hQ.isPGroup hQM
      · intro g hg _
        rw [hN] at hg ⊢
        have hg' : g⁻¹ ∉ D.M := fun hgm => hg (by simpa using D.M.inv_mem hgm)
        have h := hsp.inf_map_conj_eq_bot Nat.prime_five hQM hQ.isPGroup g⁻¹ hg'
        simpa [conjSubgroup] using h
    · subst q
      have h3Y : 3 ∣ Nat.card Y := by
        apply Nat.dvd_of_mem_primeFactors
        rw [hqfac]
        simp
      have hQLK : Q ≤ L ∨ Q ≤ K := by
        have hQOpp : Q ≤ Opp 3 Y :=
          le_pElementSubgroup_of_isPGroup Nat.prime_three hQ.isPGroup hQY
        rcases hOpp with h | h
        · exact Or.inl (hQOpp.trans h)
        · exact Or.inr (hQOpp.trans h)
      have hQsyl : IsSylowIn 3 Q Y := CFSG.ABGLocalTools.isSylowOf_iff.mp hQ
      have hQcard : Nat.card Q = 3 := by
        rcases hQLK with hQL | hQK
        · exact card_eq_three_of_isSylowIn_three_19_4 hQsyl hQL hnot9L h3Y
        · exact card_eq_three_of_isSylowIn_three_19_4 hQsyl hQK hnot9K h3Y
      have hQU : Q ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
        rcases hQLK with hQL | hQK
        · exact (hpair Q A₂ hQL hQcard hA₂K hA₂card).1
        · exact (hpair A₁ Q hA₁L hA₁card hQK hQcard).2
      have hQinU : CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M Q :=
        inU_iff_mem_uniqueSet.mpr hQU
      have hQprime : (Nat.card Q).Prime := by rw [hQcard]; exact Nat.prime_three
      refine ⟨3, Nat.prime_three, by norm_num, hQ.isPGroup, ?_, ?_, ?_⟩
      · rw [hN]
        exact hQM
      · rw [hN]
        exact S17.rankThreeGamma_le_of_inU hQinU hQcard
      · intro g hg _
        rw [hN] at hg ⊢
        exact S17.inf_conjSubgroup_eq_bot_of_inU hQinU hQprime g hg
  rw [calPMTA, hN]
  exact ⟨E1.IsE.isEAny hE', Q, hcalP, hYeq⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
