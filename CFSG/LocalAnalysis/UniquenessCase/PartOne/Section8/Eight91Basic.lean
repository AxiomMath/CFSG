module

import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SetupModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SylowCenter
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33ExceptionalRanks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Par

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ABGLocalTools (IsSylowOf)

private theorem k891basic_not_dvd_card_pCore_two {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [hk]
  intro h
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)

private theorem k891basic_barImage_mulEquiv {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQL : Q ≤ L) (hQ : IsPGroup 3 Q) :
    Nonempty (↥Q ≃* ↥(barImage L Q)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := k891basic_not_dvd_card_pCore_two L
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Q.subgroupOf L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hN hQ.comap_subtype
  have hrange : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Q.subgroupOf L).subtype).range
      = barImage L Q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact ⟨(Subgroup.subgroupOfEquivOfLe hQL).symm.trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩

private theorem k891basic_ZOf_eq_map {G : Type} [Group G] (Q : Subgroup G) :
    ZOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  rw [ZOf, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxQ, hx⟩
    refine ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hx y y.2), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun h hh => congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)⟩

theorem card_zOf_eq_card_zOf_barImage {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQL : Q ≤ L) (hQ : IsPGroup 3 Q) :
    Nat.card (ZOf Q) = Nat.card (ZOf (barImage L Q)) := by
  obtain ⟨e⟩ := k891basic_barImage_mulEquiv hQL hQ
  rw [k891basic_ZOf_eq_map Q, k891basic_ZOf_eq_map (barImage L Q),
    Subgroup.card_map_of_injective Q.subtype_injective,
    Subgroup.card_map_of_injective (barImage L Q).subtype_injective]
  exact Nat.card_congr (Subgroup.centerCongr e).toEquiv

private theorem k891basic_isSylowOf_barImage_top {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hP : IsSylowOf 3 P L) : IsSylowOf 3 (barImage L P) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hbar : barImage L P =
      (Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) Q :
        Subgroup (Bar2 L)) := by
    rw [show barImage L P =
      (P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl, ← hQ]
    exact (Sylow.coe_mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) Q).symm
  rw [hbar, CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, (Sylow.mapSurjective (QuotientGroup.mk'_surjective
    (CFSG.pCore 2 ↥L)) Q).isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact (Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) Q).not_dvd_index

theorem s891_basic
    {G : Type} [Group G] [Finite G] (D : Data G)
    (hM3 : CFSG.Open.pRank 3 D.M ≤ 3) (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n) :
    R891Basic D L S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcenter : center (Bar2 L) = ⊥ :=
    PartTwo.Inputs1719.Thm14_5.center_eq_bot_of_is3D4 hset.d4
  have hbarRank : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 :=
    pRank_three_eq_two_of_lieModel_trialityD4 hset.d4
  have hLM : L ≤ D.M := hset.mem.1.le
  have hrank : CFSG.Open.pRank 3 L = 2 := by
    have h1 : CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup L
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
      (CFSG.SectionRank.pRank_quotient_eq (G := ↥L) (p := 3) (CFSG.pCore 2 ↥L)
        (k891basic_not_dvd_card_pCore_two L)).symm
    rw [h1, h2, hbarRank]
  have hnormal : D.M ≤ normalizer (L : Set G) := by
    by_contra hnN
    obtain ⟨E, hEL, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
    have hEcard' : Nat.card E = 3 ^ 2 := by rw [hEcard, hrank]
    have hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
      rw [hcenter, Subgroup.card_bot]
      norm_num
    have h4 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.calCRankTwice D.M L hset.mem hnN
      3 Nat.prime_three (by norm_num) hZ E hEL hEel 2 hEcard'
    omega
  have hSylowL : IsSylowOf 3 (S ⊓ L) L := hset.sylow.inf_of_le_normalizer hLM hnormal
  have hzOrder : Nat.card (ZOf (S ⊓ L)) = 3 := by
    have hSylTop : IsSylowOf 3 (barImage L (S ⊓ L)) ⊤ :=
      k891basic_isSylowOf_barImage_top hSylowL
    have hZbar : Nat.card (ZOf (barImage L (S ⊓ L))) = 3 := by
      obtain ⟨S₀, B₀, hsetup⟩ := exists_r891D4Setup hset.d4
      obtain ⟨z, _, hz3, hz1, g, hZeq⟩ := hsetup.exists_zOf_eq hSylTop
      rw [hZeq, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    rw [card_zOf_eq_card_zOf_barImage hSylowL.le hSylowL.isPGroup, hZbar]
  exact ⟨hnormal, hcenter, hrank, hSylowL, hzOrder⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
