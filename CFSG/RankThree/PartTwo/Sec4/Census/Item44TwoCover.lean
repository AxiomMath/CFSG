module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Quasisimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndLift
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.RankThree.Coprime.EvenCenterSectionCover
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo Subgroup
open CFSG.Assembly.RankThreeEven (projSL localRank)

@[expose] def TwoCoverCensus : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → SectionFourHyp J →
    SectionFourHyp (J ⧸ center J) → IsPGroup 2 (center J) → Nontrivial (center J) →
    CFSG.pRank 2 J = 3 →
    (∀ q : ℕ, q.Prime → 3 < q → CFSG.pRank q (J ⧸ center J) ≤ 2) →
    (CFSG.pRank 3 (J ⧸ center J) ≤ 3 ∨ Nonempty (J ⧸ center J ≃* NativeSporadic.ON)) →
      Nonempty (J ⧸ center J ≃* NativeSporadic.M12) ∨
      (Nonempty (J ⧸ center J ≃* NativeSporadic.M22) ∧ Nat.card (center J) = 4) ∨
      Nonempty (J ⧸ center J ≃* NativeSporadic.J2) ∨
      (Nonempty (J ⧸ center J ≃* projSL 3 (GaloisField 2 2)) ∧ IsCyclic (center J) ∧
        Nat.card (center J) = 4)

theorem sectionFourHyp_subgroup {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    (H : Subgroup G) : SectionFourHyp H :=
  ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hG.kGroup H ⊥ QuotientGroup.quotientBot,
    (evenRank_subgroup_le H).trans hG.evenRank_le,
    fun p hp h3 => (localRank_subgroup_le hp H).trans_lt (hG.localRank_lt p hp h3)⟩

noncomputable def quotientTopEquiv {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    (⊤ : Subgroup G) ⧸ N.subgroupOf ⊤ ≃* G ⧸ N :=
  QuotientGroup.congr _ _ Subgroup.topEquiv (by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf])

theorem sectionFourHyp_quotient (h41 : Item4_1) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) (N : Subgroup G) [N.Normal] (hq : IsQuasisimple (G ⧸ N)) :
    SectionFourHyp (G ⧸ N) :=
  sectionFourHyp_of_mulEquiv (quotientTopEquiv N)
    (sectionFourHyp_of_section h41 hG ⊤ _
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotientTopEquiv N).symm hq))

theorem isPGroup_two_center_of_oddCore_eq_bot {X : Type*} [Group X] [Finite X]
    (hO : oddCore X = ⊥) : IsPGroup 2 (center X) := by
  intro x
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : X)).ne'
  have hy : (x : X) ^ 2 ^ a ∈ center X := pow_mem x.2 _
  have hord : orderOf ((x : X) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
  have hle : zpowers ((x : X) ^ 2 ^ a) ≤ oddCore X := by
    refine le_oddCore (normal_of_le_center (zpowers_le.mpr hy)) ?_
    rw [Nat.card_zpowers, hord]
    exact hm
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow, hle, OneMemClass.coe_one])⟩

theorem exists_central_involution_quot {G : Type} [Group G] [Finite G] {K : Subgroup G}
    [K.Normal] (hyp : PartTwoRankThreeHyp G K) :
    ∃ z ∈ center (G ⧸ oddCore G), z ≠ 1 ∧ z * z = 1 := by
  obtain ⟨p, hp, hp5, ρ, hρ, -, a₀, ha₀2, ha₀⟩ := exists_rep hyp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨(a₀ : G ⧸ oddCore G), ?_, ?_, ?_⟩
  · rw [mem_center_iff]
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have h1 : ρ (g * a₀ * (a₀ * g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, ha₀, mul_neg_one, neg_one_mul, mul_inv_cancel]
      have h2 := mk_eq_one_of_map_eq_one hρ h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h2
      exact h2
  · intro h
    have hneg : (-1 : GL (Fin 4) (ZMod p)) ≠ 1 := by
      intro h'
      have h'' : (-1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 := by
        have := congrArg (fun g : GL (Fin 4) (ZMod p) => (g : Matrix (Fin 4) (Fin 4) (ZMod p))) h'
        simpa using this
      have h00 : (-1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 =
          (1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 := by rw [h'']
      rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        calc ((2 : ℕ) : ZMod p) = 1 - (-1) := by push_cast; ring
          _ = 0 := by rw [h00, sub_self]
      exact natCast_ne_zero_of_prime_ne Nat.prime_two (by omega) h2
    have ha₀O : a₀ ∈ oddCore G := (QuotientGroup.eq_one_iff a₀).mp h
    have ha₀1 : a₀ ≠ 1 := fun h' => hneg (by rw [← ha₀, h', map_one])
    have hord : orderOf a₀ = 2 := orderOf_eq_prime (by rw [sq, ha₀2]) ha₀1
    have := odd_orderOf_of_mem_oddCore' ha₀O
    rw [hord] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  · rw [← QuotientGroup.mk_mul, ha₀2, QuotientGroup.mk_one]

theorem star_of_central_involution (h41 : Item4_1) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) (hq : IsQuasisimple (G ⧸ oddCore G)) {z : G ⧸ oddCore G}
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
  obtain ⟨-, h2⟩ := h41 H hHS ⊤ _ hlayer
  have hSrank : ∀ q : ℕ, q.Prime → CFSG.pRank q ((G ⧸ oddCore G) ⧸ center (G ⧸ oddCore G)) =
      CFSG.Open.pRank q (⊤ : Subgroup ((⊤ : Subgroup H) ⧸ φ.ker.subgroupOf ⊤)) := by
    intro q hq'
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact (pRank_congr_mulEquiv hq'.one_lt e).symm
  have hHrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup H) ≤ localRank q G :=
    fun q hq' hq2 => by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact pRank_le_localRank_of_centralizes hq' hq2 hwo hHw
  refine ⟨fun q hq' hq3 => ?_, ?_⟩
  · have hle : CFSG.Open.pRank q (⊤ : Subgroup H) ≤ 2 := by
      have := hG.localRank_lt q hq' hq3
      have := hHrank q hq' (by omega)
      omega
    rw [hSrank q hq']
    exact ((h2 q hq' (by omega)).1 hq3).trans hle
  · have hle : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) H hH2).trans hG.evenRank_le
    rcases (h2 3 Nat.prime_three hle).2 rfl
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSq) with h3 | ⟨⟨f⟩, -⟩
    · left
      rw [hSrank 3 Nat.prime_three]
      exact h3.trans hle
    · exact Or.inr ⟨e.symm.trans f⟩

theorem quasisimpleCensus_of (h41 : Item4_1) (hcen : TwoCoverCensus) : QuasisimpleCensus := by
  intro G _ _ K _ hyp hq
  obtain ⟨z, hz, hz1, hz2⟩ := exists_central_involution_quot hyp
  obtain ⟨hG, -, -, -, -, -, -, h3, -⟩ := hyp
  have hX : SectionFourHyp (G ⧸ oddCore G) := sectionFourHyp_quotient h41 hG (oddCore G) hq
  have hZ2 : IsPGroup 2 (center (G ⧸ oddCore G)) :=
    isPGroup_two_center_of_oddCore_eq_bot (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot G)
  have hZnt : Nontrivial (center (G ⧸ oddCore G)) :=
    ⟨⟨⟨z, hz⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have hm2 : CFSG.pRank 2 (G ⧸ oddCore G) = 3 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
      (fun h2 => (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore G))
        (even_iff_two_dvd.mpr h2)), CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact h3
  obtain ⟨hstar, hstar3⟩ := star_of_central_involution h41 hG hq hz hz1 hz2
  exact hcen _ hq hX (sectionFourHyp_quotient_center h41 hX hq) hZ2 hZnt hm2 hstar hstar3

end CFSG.RankThree.PartTwo.Sec4.Census
