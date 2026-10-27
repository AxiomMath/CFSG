module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KGroupSporadic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverCenterOddHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineteen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
public import CFSG.Quasithin.H13.NQBlockLayerProduct
public import CFSG.Quasithin.Background.E2TwoLieQuotBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.Quasithin.Background.E2TwoLieQuotLift
public import CFSG.Quasithin.Background.SmithB45HatA6Out
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


@[expose] def Gap17_18P (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L →
    2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M →
        (CFSG.Open.pRank 3 L ≤ 2 → ∃ X : Subgroup G, F11.InP11 D X) ∧
        (IsSpor (BarInf L) .ONan → ¬ (L.subgroupOf D.M).Normal →
          ∃ X : Subgroup G, F11.InP11 D X)

theorem conjSetOf_calC_and_isJ1 {M L : Subgroup G} (hL : L ∈ calC M) (hJ : IsJ1 (Bar2 L)) :
    ∀ K ∈ UC22.conjSetOf M L, K ∈ calC M ∧ IsJ1 (Bar2 K) := by
  intro K hK
  refine ⟨UC22.uc22p2214_calC_of_mem_conjSetOf hL hK, ?_⟩
  obtain ⟨m, -, rfl⟩ := hK
  obtain ⟨e⟩ := UC22.uc22p20d_bar2_conj m L
  obtain ⟨eJ⟩ := hJ
  exact ⟨e.symm.trans eJ⟩

theorem exists_three_distinct_conj_of_isJ1 {M L : Subgroup G}
    (hL : L ∈ calC M) (hJ : IsJ1 (Bar2 L))
    (h3 : 2 < CFSG.Open.pRank 3 (UC22.conjClosure M L)) :
    ∃ K₁ ∈ UC22.conjSetOf M L, ∃ K₂ ∈ UC22.conjSetOf M L, ∃ K₃ ∈ UC22.conjSetOf M L,
      K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ := by
  classical
  have hp1 : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isJ1_bar2 hJ
  have hne : UC22.conjClosure M L ≠ L := by
    intro h
    rw [h, hp1] at h3
    omega
  obtain ⟨K, hKS, hKL⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hne
  by_cases hthree : ∃ K' ∈ UC22.conjSetOf M L, K' ≠ L ∧ K' ≠ K
  · obtain ⟨K', hK'S, hK'L, hK'K⟩ := hthree
    exact ⟨L, self_mem_conjSetOf M L, K, hKS, K', hK'S, hKL.symm, hK'L.symm, hK'K.symm⟩
  · exfalso
    push Not at hthree
    have hthree' : ∀ K' ∈ UC22.conjSetOf M L, K' = L ∨ K' = K := by
      intro K' hK'
      by_cases h : K' = L
      · exact Or.inl h
      · exact Or.inr (hthree K' hK' h)
    have hclosure : UC22.conjClosure M L = L ⊔ K := by
      refine le_antisymm ?_ ?_
      · refine iSup₂_le fun A hA => ?_
        rcases hthree' A hA with hAL | hAK
        · rw [hAL]; exact le_sup_left
        · rw [hAK]; exact le_sup_right
      · exact sup_le (TwelveTwentyThree.le_conjClosure M L)
          (le_iSup₂_of_le K hKS le_rfl)
    obtain ⟨hKM, hJK⟩ := conjSetOf_calC_and_isJ1 hL hJ K hKS
    have hKY : K ≤ Subgroup.normalizer (L : Set G) := calC_le_normalizer_of_ne hL hKM hKL.symm
    have hYL : L ≤ Subgroup.normalizer (K : Set G) := calC_le_normalizer_of_ne hKM hL hKL
    have hc : ⁅K, L⁆ ≤ pCoreOf 2 K ⊓ pCoreOf 2 L := calC_commutator_le_of_ne hKM hL hKL
    have hsimpleK : IsSimpleGroup (Bar2 K) := (kJ1_holds (Bar2 K) hJK).2.1
    have hnabK : ∃ a b : Bar2 K, a * b ≠ b * a := by
      have hcard : Nat.card (Bar2 K) = 175560 := (kJ1_holds (Bar2 K) hJK).1
      exact @CFSG.Quasithin.E2.exists_noncomm_of_isSimpleGroup (Bar2 K) _ _ hsimpleK
        (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    have hrank := @CFSG.Quasithin.H13.NQBlock.commuting_product_pRank G _ _ K L
      hKY hYL hc hsimpleK hnabK 3 Nat.prime_three (by norm_num)
    have hKq : CFSG.pRank 3 (↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        pRank_bar2_eq_of_odd (Y := K) Nat.prime_three (by norm_num)]
      exact pRank_three_eq_one_of_isJ1_bar2 hJK
    have hLq : CFSG.pRank 3 ↥L = 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact hp1
    have hrank2 : CFSG.Open.pRank 3 (K ⊔ L) = 2 := by
      rw [hKq, hLq, CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hrank
      omega
    have : CFSG.Open.pRank 3 (UC22.conjClosure M L) = 2 := by
      rw [hclosure, sup_comm]
      exact hrank2
    omega

theorem k_eq_one_of_isJ1 (D : Data G) (h82 : F08.R82 D) {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hJ : IsJ1 (Bar2 L))
    (h3 : 2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L)) : D.k = 1 := by
  classical
  obtain ⟨K₁, hK₁, K₂, hK₂, K₃, hK₃, h12, h13, h23⟩ :=
    exists_three_distinct_conj_of_isJ1 c.mem_calC hJ h3
  obtain ⟨hK₁M, j₁⟩ := conjSetOf_calC_and_isJ1 c.mem_calC hJ K₁ hK₁
  obtain ⟨hK₂M, j₂⟩ := conjSetOf_calC_and_isJ1 c.mem_calC hJ K₂ hK₂
  obtain ⟨hK₃M, j₃⟩ := conjSetOf_calC_and_isJ1 c.mem_calC hJ K₃ hK₃
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    h82 _ (UC22.R8107Odd.hyp81_of_three_rankOne hK₁M hK₂M hK₃M h12 h13 h23
      (pRank_three_eq_one_of_isJ1_bar2 j₁) (pRank_three_eq_one_of_isJ1_bar2 j₂)
      (pRank_three_eq_one_of_isJ1_bar2 j₃))
  have hk2 : D.k ≠ 2 := fun hk => ((Data.k_eq_two_iff D).mp hk) hstr
  have h1 : 1 ≤ D.k := TwelveShort.one_le_k D
  have h2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  omega


section Certificates


theorem k_eq_one_of_pRank_le_two
    (D : Data G) (h82 : F08.R82 D) (h880 : F08.R880 D)
    (hSg : UC6S846.SigmaStd D) {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h3 : 2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L))
    (h2 : CFSG.Open.pRank 3 L ≤ 2) : D.k = 1 := by
  classical
  have hK1 : Inputs1719.KSporadicThreeRank := PartOne.Section8.kSporadicThreeRank_holds
  let s : TauCeti.SporadicName := c.sporadic.choose
  have hspor : IsSpor (BarInf L) s := c.sporadic.choose_spec
  let eS : BarInf L ≃* CFSG.Blueprint.NativeSporadic.Carrier s := Classical.choice hspor
  obtain ⟨eBI⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := UC22.uc22p20p_odd_center_bar2 ↥L
  have hspq : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) s := ⟨eBI.symm.trans eS⟩
  by_cases hZ : Subgroup.center (Bar2 L) = ⊥
  ·
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := c.mem_calC.2.2
    have hsporBar : IsSpor (Bar2 L) s := by
      obtain ⟨e2⟩ := UC22.uc22p21k_barInf_equiv_of_center_bot hq hZ
      exact ⟨e2.symm.trans eS⟩
    by_cases h2eq : CFSG.Open.pRank 3 L = 2
    · have hne : UC22.conjClosure D.M L ≠ L := fun h => by rw [h, h2eq] at h3; omega
      obtain ⟨K, hK, hKL⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hne
      have h4M : 4 ≤ CFSG.Open.pRank 3 D.M :=
        four_le_pRank_three_of_two_conj_of_not_three_dvd_center
          c.mem_calC (self_mem_conjSetOf D.M L) hK hKL.symm h2eq
          (fun h => by rw [hZ, Subgroup.card_bot] at h; norm_num at h)
      exact Data.k_eq_one_of_isStronglyPEmbedded D
        (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC c.mem_calC)
          (hSg.four_mem 3 Nat.prime_three (by norm_num) h4M))
    · have hle1 : CFSG.Open.pRank 3 L ≤ 1 := by omega
      have : Nontrivial (BarInf L) := by
        have := hq.2.toNontrivial
        exact eBI.toEquiv.nontrivial
      have hposBI : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) :=
        Inputs1719.k_SporadicThreeRankPos_holds (BarInf L) s hspor
      obtain ⟨e2⟩ := UC22.uc22p21k_barInf_equiv_of_center_bot hq hZ
      have hposBar : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e2]
        exact hposBI
      have hup : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = CFSG.Open.pRank 3 L :=
        pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)
      have hbar1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 1 := by omega
      have hbar1C : CFSG.pRank 3 (⊤ : Subgroup (Bar2 L)) = 1 := by
        rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
        exact hbar1
      have hsJ1 : s = .J1 := (hK1 (Bar2 L) s hsporBar).1.mpr hbar1C
      have hJ : IsJ1 (Bar2 L) := by
        unfold IsJ1
        rw [← hsJ1]
        exact hsporBar
      exact k_eq_one_of_isJ1 D h82 c hJ h3
  ·
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := c.mem_calC.2.2
    have hleBar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ 2 := by
      rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
      exact h2
    have hCov := Inputs1719.k_SporadicCoverThreeRank_holds (Bar2 L) s hq hodd hspq hleBar
    have hpos : 1 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) := by
      have : Nontrivial (BarInf L) := by
        have := hq.2.toNontrivial
        exact eBI.toEquiv.nontrivial
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eBI]
      exact Inputs1719.k_SporadicThreeRankPos_holds (BarInf L) s hspor
    have hne1 : CFSG.Open.pRank 3
        (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) ≠ 1 := by
      intro h1
      have h1C : CFSG.pRank 3
          (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 1 := by
        rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
        exact h1
      have hsJ1 : s = .J1 :=
        (hK1 (Bar2 L ⧸ Subgroup.center (Bar2 L)) s hspq).1.mpr h1C
      have hspqJ1 : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) .J1 := by
        rw [← hsJ1]
        exact hspq
      exact hZ (Inputs1719.k_J1IsCenterless_holds (Bar2 L) hq hodd hspqJ1)
    have hrank2 : CFSG.Open.pRank 3
        (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 2 := by omega
    have hrank2C : CFSG.pRank 3
        (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 2 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      exact hrank2
    have hslist := (hK1 (Bar2 L ⧸ Subgroup.center (Bar2 L)) s hspq).2.mpr hrank2C
    have hKc := Inputs1719.k_SporadicCoverCenterOdd_holds (Bar2 L) s hq hodd hspq hslist
    obtain ⟨hsM22, hZcard⟩ := hKc.resolve_left hZ
    have hqC : CFSG.IsQuasisimple (Bar2 L) := CFSG.Quasithin.E2.isQuasisimple_of_open hq
    have hspqM22 : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) .M22 := by
      rw [← hsM22]
      exact hspq
    have hM22Z3 : F08.IsM22Z3 (Bar2 L) := ⟨hqC, hZcard, hspqM22⟩
    have hList : F08.List880 (Bar2 L) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM22Z3)))))))
    by_contra hk1
    have hk2 : D.k = 2 := by
      have h1 := TwelveShort.one_le_k D
      have h2' := TwelveSeven.k_le_two D
      omega
    have hnstr : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
      (Data.k_eq_two_iff D).mp hk2
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
    have hJ2 : IsSpor (Bar2 L) .J2 := (h880 L c.mem_calC hList hnstr P hP).1
    exact (Inputs1719.k_M22OddCover_holds (Bar2 L) hq hodd hspqM22).1 hJ2

theorem gap17_18ReductionResidual_of
    (D : Data G) (V₀ V : Subgroup G)
    (h82 : F08.R82 D) (h880 : F08.R880 D)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hSg : UC6S846.SigmaStd D)
    (hP : Gap17_18P D V₀ V) :
    Gap17_18ReductionResidual D V₀ V := by
  intro L c h3 hcase
  have hk : D.k = 1 := by
    rcases hcase with h2 | ⟨hON, -⟩
    · exact k_eq_one_of_pRank_le_two D h82 h880 hSg c h3 h2
    · exact k_eq_one_of_pRank_gt_two D V₀ V h82 c
        (two_lt_pRank_three_of_isSpor_ONan D c hON)
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra h
    exact absurd ((Data.k_eq_two_iff D).2 h) (by omega)
  refine ⟨hk, ?_⟩
  by_cases hON : IsSpor (BarInf L) .ONan
  · by_cases hN : (L.subgroupOf D.M).Normal
    · exact Or.inr ⟨hN, hON⟩
    · exact Or.inl ((hP L c h3 hstr).2 hON hN)
  · by_cases h2 : CFSG.Open.pRank 3 L ≤ 2
    · exact Or.inl ((hP L c h3 hstr).1 h2)
    · push Not at h2
      exact Or.inl (exists_inP11_of_three_rank_gt_two D V₀ V hKS1 hstr c h2 hON)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

