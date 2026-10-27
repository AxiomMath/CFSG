module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_38_holds
    (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (h21 : R1621 D)
    (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (hσ3 : SigmaThree D) (hrank : R16_38_rankGap D)
    (hm2 : R16_38_m2Gap D) (hm3 : R16_38_m3Gap D) : R16_38 D := by
  intro V₀ V L hV hS m hm i him
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro X ⟨g, rfl, hO⟩
  have hn : m + i + 2 ≤ 2 * m := by omega
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  obtain ⟨a, haM, haq, e, he1, heQ, hfix⟩ :=
    r38_geometry D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK
  have haN : a ∈ Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    Mbar_le_normalizer_lBar hS S hSω haM
  have hq : (2 ^ m - 1).Prime := by
    rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  obtain ⟨E, haE, hEle, hcomm, hexp, hcard⟩ :=
    S.exists_elemAbelian_of_singular_fixed hSK hq haN haq he1 heQ hfix
  rw [hSω] at hEle
  have hlift : 3 ≤ CFSG.Open.pRank (2 ^ m - 1) D.M :=
    hrank hSg h1219 h21 h22 h61 hext h5 V₀ V L hV hS m hm _ hn g hO hq a E haE haM hEle hcomm
      hexp hcard
  rcases hm with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · exact hm2 hSg h1219 h21 h22 h61 hext h5 h76 h614 V₀ V L hV hS hc _ hn g hO
      (by simpa using hlift)
  · by_cases he : CFSG.Open.evenRank G = 3
    · have hsig : D.sig = {3} := hc.2.2
      have h3mem : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
      have hm3 : CFSG.Open.pRank 3 D.M = 3 :=
        le_antisymm
          (he ▸ CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
            (by norm_num) D.M D.maxLocal.1)
          (hext.three_le 3 h3mem)
      have h7 : CFSG.Open.pRank 7 D.M ≤ 2 :=
        pRank_le_two_of_twoLocal D hext hσ3 hsig hm3 (by norm_num) (by norm_num) D.maxLocal.1
      have h7' : 3 ≤ CFSG.Open.pRank 7 D.M := by simpa using hlift
      omega
    · exact hm3 hSg h1219 h21 h22 h61 hext h5 V₀ V L hV hS hc _ hn g hO he
        (by simpa using hlift)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
