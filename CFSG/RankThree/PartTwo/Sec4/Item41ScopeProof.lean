module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
public import CFSG.RankThree.PartTwo.Sec4.Item41PRankNarrow41
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndMain
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.RankThree.PartTwo.NotationBlocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo Subgroup
open CFSG.Assembly.RankThreeEven (projSL localRank)

theorem not_three_dvd_card_oddCore_of_hyp {G : Type} [Group G] [Finite G] {K : Subgroup G}
    [K.Normal] (hyp : PartTwoRankThreeHyp G K) : ¬ 3 ∣ Nat.card (oddCore G) := by
  obtain ⟨-, hperf, -, hsimple, hK3, -⟩ := hyp
  have : Group.IsPerfect G := hperf
  have : IsSimpleGroup (G ⧸ K) := hsimple
  exact fun h => hK3 (h.trans (Subgroup.card_dvd_of_le oddCore_le_of_isSimpleGroup))

theorem not_mem_center_of_orderOf_eq_three {G : Type} [Group G] [Finite G]
    (hO : ¬ 3 ∣ Nat.card (oddCore G)) {g : G} (hg : orderOf g = 3) :
    (g : G ⧸ oddCore G) ∉ center (G ⧸ oddCore G) := by
  intro hc
  have hZ2 : IsPGroup 2 (center (G ⧸ oddCore G)) :=
    isPGroup_two_center_of_oddCore_eq_bot
      (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot G)
  obtain ⟨k, hk⟩ := hZ2 ⟨(g : G ⧸ oddCore G), hc⟩
  have h1 : (g : G ⧸ oddCore G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : (g : G ⧸ oddCore G) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hg, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hd : orderOf (g : G ⧸ oddCore G) ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  have hgO : g ∈ oddCore G := (QuotientGroup.eq_one_iff g).mp hd
  have h3 := orderOf_dvd_natCard (⟨g, hgO⟩ : oddCore G)
  rw [Subgroup.orderOf_mk, hg] at h3
  exact hO h3

theorem star_of_central_involution_narrow41 (h3 : Item4_1PRankLargePrime) {G : Type}
    [Group G] [Finite G] (hG : SectionFourHyp G) (hO : ¬ 3 ∣ Nat.card (oddCore G))
    (hq : IsQuasisimple (G ⧸ oddCore G)) {z : G ⧸ oddCore G}
    (hz : z ∈ center (G ⧸ oddCore G)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    (∀ q : ℕ, q.Prime → 3 < q →
      CFSG.pRank q ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G)) ≤ 2) ∧
    (CFSG.pRank 3 ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G)) ≤ 3 ∨
      Nonempty ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) ≃* NativeSporadic.ON)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (oddCore G) with hπ
  have hQ2 : IsPGroup 2 (zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq, hz2]) hz1
  have hQn : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hz)
  obtain ⟨R, hRQ, hRinj, hR2, hRN⟩ := exists_lift_two (zpowers z) hQ2
  obtain ⟨w, hw, hπw⟩ : z ∈ R.map π := by rw [hRQ]; exact mem_zpowers z
  have hlift : ∀ r ∈ R, ∀ r' ∈ R, π r = π r' → r = r' := fun r hr r' hr' h =>
    eq_of_mk_eq hRinj hr hr' h
  have hww : w * w = 1 :=
    hlift _ (mul_mem hw hw) _ (one_mem R) (by rw [map_mul, hπw, hz2, map_one])
  have hw1 : w ≠ 1 := fun h => hz1 (by rw [← hπw, h, map_one])
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq, hww]) hw1
  set H := normalizer (R : Set G) with hH
  have hHw : ∀ h ∈ H, h * w = w * h := by
    intro h hh
    have hmem : h * w * h⁻¹ ∈ R := (mem_normalizer_iff.mp hh w).mp hw
    have h1 : h * w * h⁻¹ = w := hlift _ hmem _ hw (by
      rw [map_mul, map_mul, map_inv, hπw, mem_center_iff.mp hz (π h), mul_inv_cancel_right])
    calc h * w = h * w * h⁻¹ * h := by group
      _ = w * h := by rw [h1]
  have hH2 : CFSG.Assembly.IsTwoLocal H := ⟨R, fun h => hw1 (by
    rw [h] at hw
    exact (mem_bot).mp hw), hR2, rfl⟩
  have hHS : SectionFourHyp H := sectionFourHyp_subgroup hG H
  let φ : H →* (G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) :=
    (QuotientGroup.mk' (center (G ⧸ oddCore G))).comp (π.comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center (G ⧸ oddCore G)) y
    have hx : x ∈ H.map π := by rw [hRN hQn]; exact mem_top x
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨⟨h, hh⟩, rfl⟩
  let e : (⊤ : Subgroup H) ⧸ φ.ker.subgroupOf ⊤ ≃* (G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G) :=
    (quotientTopEquiv φ.ker).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have : IsSimpleGroup ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G)) := hq.2.1
  have hSq : IsQuasisimple ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hq.2.2).1
  have hlayer := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSq)
  have hSrank : ∀ q : ℕ, q.Prime → CFSG.pRank q ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G)) =
      CFSG.Open.pRank q (⊤ : Subgroup ((⊤ : Subgroup H) ⧸ φ.ker.subgroupOf ⊤)) := by
    intro q hq'
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact (pRank_congr_mulEquiv hq'.one_lt e).symm
  have hHrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup H) ≤ localRank q G :=
    fun q hq' hq2 => by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact pRank_le_localRank_of_centralizes hq' hq2 hwo hHw
  refine ⟨fun q hq' hq3 => ?_, Or.inl ?_⟩
  · have hle : CFSG.Open.pRank q (⊤ : Subgroup H) ≤ 2 := by
      have := hG.localRank_lt q hq' hq3
      have := hHrank q hq' (by omega)
      omega
    rw [hSrank q hq']
    exact (h3 H hHS ⊤ _ hlayer q hq' hq3 (by omega)).trans hle
  · have hle : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) H hH2).trans hG.evenRank_le
    have hker : ¬ 3 ∣ Nat.card φ.ker := by
      intro h3k
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3k
      have hxo : orderOf ((x : H) : G) = 3 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
      have hxc : (((x : H) : G) : G ⧸ oddCore G) ∈ center (G ⧸ oddCore G) := by
        have hmem : φ (x : H) = 1 := x.2
        exact (QuotientGroup.eq_one_iff (((x : H) : G) : G ⧸ oddCore G)).mp hmem
      exact not_mem_center_of_orderOf_eq_three hO hxo hxc
    rw [← pRank_congr_mulEquiv (p := 3) (by norm_num)
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ),
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _ hker,
      CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hle

theorem quasisimpleCensus_of_narrow41 (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover)
    (h3 : Item4_1PRankLargePrime) (hcen : TwoCoverCensus) : QuasisimpleCensus := by
  intro G _ _ K _ hyp hq
  obtain ⟨z, hz, hz1, hz2⟩ := exists_central_involution_quot hyp
  have hO := not_three_dvd_card_oddCore_of_hyp hyp
  obtain ⟨hG, -, -, -, -, -, -, hm3, -⟩ := hyp
  have hX : SectionFourHyp (G ⧸ oddCore G) :=
    Item41Narrow.sectionFourHyp_quotient h1 hG (oddCore G) hO hq
  have hZ2 : IsPGroup 2 (center (G ⧸ oddCore G)) :=
    isPGroup_two_center_of_oddCore_eq_bot (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot G)
  have hZnt : Nontrivial (center (G ⧸ oddCore G)) :=
    ⟨⟨⟨z, hz⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have hm2 : CFSG.pRank 2 (G ⧸ oddCore G) = 3 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
      (fun hd => (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore G))
        (even_iff_two_dvd.mpr hd)), CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hm3
  obtain ⟨hstar, hstar3⟩ := star_of_central_involution_narrow41 h3 hG hO hq hz hz1 hz2
  exact hcen _ hq hX (Item41Narrow.sectionFourHyp_quotient_center h1 h2 hX hq) hZ2 hZnt hm2
    hstar hstar3

end CFSG.RankThree.PartTwo.Sec4.Census
