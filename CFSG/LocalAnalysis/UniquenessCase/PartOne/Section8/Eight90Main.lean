module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S123
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Center
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90T7Uc410
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

theorem r890_le_of_isTwoLocal {G : Type} [Group G] [Finite G] {M X N : Subgroup G}
    (hMX : calMOf X = {M}) (hN : IsTwoLocal N) (hXN : X ≤ N) : N ≤ M := by
  obtain ⟨N', hNN', hmax⟩ :=
    (Set.toFinite {H : Subgroup G | IsTwoLocal H}).exists_le_maximal (a := N) hN
  have hN'mem : N' ∈ calMOf X := by
    refine ⟨⟨hmax.prop, fun H hH hle => ?_⟩, hXN.trans hNN'⟩
    exact (hmax.eq_of_le hH hle).symm
  rw [hMX] at hN'mem
  exact hNN'.trans (le_of_eq hN'mem)

theorem r890_theorem5e3 :
    ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
      Cfg890 D L P J Y n → calMOf (perfInter890 J (centralizer (Y : Set G))) = {D.M} →
      (∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ normalizer (Y : Set G) ≤ normalizer (T : Set G)) →
      normalizer (Y : Set G) ≤ D.M := by
  intro G _ _ D L P J Y n _ hMK ⟨T, hT, hT2, hYT⟩
  have hKY : perfInter890 J (centralizer (Y : Set G)) ≤ normalizer (Y : Set G) := fun k hk => by
    obtain ⟨k', -, rfl⟩ := hk
    exact Subgroup.centralizer_le_normalizer _ k'.2.2
  exact hYT.trans (r890_le_of_isTwoLocal hMK ⟨T, hT, hT2, rfl⟩ (hKY.trans hYT))

theorem r890_lnormal : LNormal_890 := by
  intro G _ _ D L P hset h882 h885
  rcases h882 L P hset with h | ⟨h, -⟩
  · exact h
  · have hno := not_three_dvd_center_of_isSpor_J2 (h885 L P hset).1
    rcases h with ⟨-, h3, -⟩ | ⟨-, h3, -⟩ | ⟨-, h3, -⟩ <;>
      exact (hno (Dvd.intro 1 (by omega))).elim

theorem r890_pCoreOf_ne_bot_of_fstar {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hF : Fstar K = pCoreOf 2 K) (hK : K ≠ ⊥) : pCoreOf 2 K ≠ ⊥ := by
  intro hbot
  rw [hbot] at hF
  have hF1 : genFittingFStar ↥K = ⊥ := by
    have h : (genFittingFStar ↥K).map K.subtype = ⊥ := hF
    rw [Subgroup.map_eq_bot_iff, K.ker_subtype] at h
    exact le_bot_iff.mp h
  have hc := CFSG.Adapters.generalized_fitting_self_centralizing ↥K
  rw [hF1] at hc
  refine hK (Subgroup.eq_bot_of_card_eq K ?_)
  have : Subsingleton ↥K := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ Subgroup.centralizer ((⊥ : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh]
      simp
    have hb : b ∈ Subgroup.centralizer ((⊥ : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh]
      simp
    have ha' := hc ha
    have hb' := hc hb
    rw [Subgroup.mem_bot] at ha' hb'
    rw [ha', hb']
  exact Nat.card_unique

theorem r890_fstarNeBot :
    ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (n : ℕ), IsSz (Bar2 K) n →
      Fstar K = pCoreOf 2 K → pCoreOf 2 K ≠ ⊥ := by
  intro G _ _ K n hSz hF
  refine r890_pCoreOf_ne_bot_of_fstar hF fun h0 => ?_
  have h5 := PartTwo.Inputs1719.FourteenEight.five_dvd_card_of_isSz hSz
  have h5' : 5 ∣ Nat.card ↥K := h5.trans (Subgroup.card_quotient_dvd_card _)
  rw [h0, Subgroup.card_bot] at h5'
  omega

theorem r890_prop3_5_of_leaves (h31 : Lemma3_1_890) (h32 : Lemma3_2a_890) (h3B : Y3B_890)
    (hJ3 : J2OrderThree_890) (hQ : QuasiOfFstarNe_890) (h2c : Step2Comm_890)
    (hCh : ChiefFactorExists_890) (h5 : Step5_890) (h6 : Step6_890) :
    Prop3_5_890 := by
  have hFne := r890_fstarNeBot
  intro hFix G _ _ D L P J Y n cfg hYZ h885 h886 h889
  obtain ⟨hcov, hperf, hO2, hsimp, hSz⟩ :=
    h32 G D L P J Y n cfg h889 (h31 G D L P J Y n cfg h885)
  have hF : Fstar (perfInter890 J (centralizer (Y : Set G))) =
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) := by
    by_contra hne
    obtain ⟨-, hcent⟩ := hQ G _ hperf hsimp hne
    have hW := r890_commutator_eq_bot_of_perfect hperf
      ((h2c G D L P J Y n cfg).trans (by rw [← hO2]; exact hcent))
    obtain ⟨A, B, hch, hJ, hOJ, hOL⟩ := hCh G D L P J Y n cfg
    obtain ⟨a, ha, haB, hfix⟩ :=
      h6 hFix G D L P J Y n cfg h885 h889 A B hch hOL
        (h3B hJ3 G D L P J Y n cfg hYZ h885 h886 h889)
    exact haB (h5 G D L P J Y n cfg h889 A B hch hOJ hJ hcov hW a ha hfix)
  exact ⟨hperf, hSz, hFne G _ n hSz hF, hF⟩

theorem r890_lemma4a1_of_leaves (hSet : PUSetup_890) (hCore : PUJ2Core_890) (hNoFF : J2NoFF_890)
    (hOff : PUJ2Offender_890) (hNorm : PUNormalizer_890) {G : Type} [Group G] [Finite G]
    {D : Data G} {L P J Y : Subgroup G} {n : ℕ}
    (cfg : Cfg890 D L P J Y n) (h869 : F08.R869 D) (h885 : PartOne.Section8.R885 D)
    (h31 : ⁅L, J⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 J) {R : Subgroup G}
    (hR : IsSylowOf 2 R (F08.CentOverO2 D.M J)) : normalizer (R : Set G) ≤ D.M := by
  obtain ⟨hRX, hLX, hFX⟩ := hSet G D L P J Y n cfg h31 R hR
  obtain ⟨C, hC, hCR, hRC, hXC⟩ :=
    hCore hNoFF hOff G L R cfg.set880.mem.2.1 (h885 L P cfg.set880).1 hRX hLX hFX
  have hR2 : IsPGroup 2 R := by
    obtain ⟨Q, hQ⟩ := hR
    rw [← hQ]
    exact Q.isPGroup'.map _
  exact hRC.trans (hNorm G D L P J Y n cfg h869 h885 C hC (hR2.to_le hCR)
    (le_sup_left.trans hXC))

theorem r890_pairStep_of_leaves (h31 : Lemma3_1_890) (h32 : Lemma3_2a_890)
    (h5b1 : Lemma5b1_890) (hSyl : Lemma5b1Syl_890) (h41 : Lemma41_890)
    (h42 : Lemma42_890) (hSet : PUSetup_890) (hCore : PUJ2Core_890) (hNoFF : J2NoFF_890)
    (hOff : PUJ2Offender_890) (hNorm : PUNormalizer_890) : PairStep_890 := by
  have hFne := r890_fstarNeBot
  intro G _ _ D L P J Y n cfg _ _ h869 _ h885 _ _ h889 hF hSz hne
  set K := perfInter890 J (centralizer (Y : Set G)) with hKdef
  have hL31 := h31 G D L P J Y n cfg h885
  obtain ⟨hcov, -, hO2, -, -⟩ := h32 G D L P J Y n cfg h889 hL31
  have hKJ : K ≤ J := fun k hk => by
    obtain ⟨k', -, rfl⟩ := hk
    exact k'.2.1
  have hKM : K ≤ D.M := hKJ.trans cfg.memJ.1.le
  have hMmem : D.M ∈ calMOf K := ⟨D.maxLocal, hKM⟩
  obtain ⟨N₀, hN₀, hN₀M⟩ : ∃ N ∈ calMOf K, N ≠ D.M := by
    by_contra h
    push Not at h
    exact hne (Set.eq_singleton_iff_unique_mem.2 ⟨hMmem, h⟩)
  have hpair₀ : KPair_890 D K N₀ (pCoreOf 2 K) :=
    ⟨hN₀, hN₀M, le_inf ((CFSG.openPCoreOf_le 2 K).trans hN₀.2)
        ((CFSG.openPCoreOf_le 2 K).trans hKM),
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K, hFne G K n hSz hF,
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K⟩
  obtain ⟨⟨N, R⟩, hNR, hmaxc⟩ := Set.exists_max_image
    {x : Subgroup G × Subgroup G | KPair_890 D K x.1 x.2} (fun x => Nat.card x.2)
    (Set.toFinite _) ⟨⟨N₀, pCoreOf 2 K⟩, hpair₀⟩
  have hmax : ∀ N' R' : Subgroup G, KPair_890 D K N' R' → Nat.card R' ≤ Nat.card R :=
    fun N' R' h => hmaxc ⟨N', R'⟩ h
  obtain ⟨hN, hNM, hRNM, hR2, hR1, hKR⟩ := hNR
  have hKN : K ≤ N := hN.2
  have hmaxNM : IsMaxKInv_890 K (N ⊓ D.M) R := by
    refine ⟨hRNM, hR2, hKR, fun R' hRR' hR'H hR'2 hKR' => ?_⟩
    have hp : KPair_890 D K N R' := ⟨hN, hNM, hR'H, hR'2, ne_bot_of_le_ne_bot hR1 hRR', hKR'⟩
    exact (Subgroup.eq_of_le_of_card_ge hRR' (hmax N R' hp)).symm
  obtain ⟨hKNn, hKNsz⟩ := h5b1 G D L P J Y n cfg hcov hO2 hSz N hKN
  refine ⟨N, hN, hNM, hKNn, hKNsz, R, hSyl G D L P J Y n cfg hcov hO2 N R hKN hmaxNM, ?_⟩
  by_cases hM : IsMaxKInv_890 K D.M R
  · exact r890_lemma4a1_of_leaves hSet hCore hNoFF hOff hNorm cfg h869 h885 hL31
      (h41 G D L P J Y n cfg hcov hO2 R hM)
  · exact h42 G D K N R ⟨hN, hNM, hRNM, hR2, hR1, hKR⟩ hmax hM

theorem r890_of_lanes {G : Type}
    [Group G] [Finite G] (D : Data G)
    (h11 : Lemma1_1_890) (hLn : LNormal_890) (h22 : Prop2_2_890) (h35 : Prop3_5_890)
    (h57 : Theorem5d7_890) (hY12 : Y12_890) (h5e1 : Lemma5e1_890) (h5e2 : Lemma5e2_890)
    (hFix : J2ThreeBFix_890) (hK318 : UCK.K318) (hSch : UCK.KSch)
    (hCat : PartTwo.Inputs1719.K_CatalogueThreePrimeSz)
    (hSLB : CFSG.RankThree.PartOne.N143.SectionListBound)
    (h847 : UC22.R847ThinNe3 D) (h61 : UC6.R6_1 D) (h869 : F08.R869 D)
    (h856 : PartOne.Section8.R856 D) (h881 : PartOne.Section8.R881 D)
    (h882 : PartOne.Section8.R882 D) (h885 : PartOne.Section8.R885 D)
    (h886 : PartOne.Section8.R886 D) (h887 : PartOne.Section8.R887 D)
    (h888 : PartOne.Section8.R888 D) (h889 : PartOne.Section8.R889 D)
    (hJ2 : PartOne.Section8.J2NotSL3PiType) :
    PartOne.Section8.R890 D := by
  refine h11 G D h856 h881 h885 h886 h887 h888 h889 hJ2 ?_
  intro L P hset hns Y hYP hY3 hYZ
  have hLM := hLn G D L P hset h882 h885
  obtain ⟨J, n, hJ, hJM, hJC, hSzJ, hn3, hnodd⟩ := h22 hK318 hCat G D L P hset hLM h885 h889 hns
  have hne : Y ≠ ZOf (P ⊓ L) := by
    rintro rfl
    exact hYZ ⟨1, D.M.one_mem, by ext x; simp⟩
  have cfg : Cfg890 D L P J Y n := ⟨hset, hLM, hJ, hJM, hJC, hSzJ, hYP, hY3, hne⟩
  obtain ⟨hperf, hSzK, hO2, hF⟩ := h35 hFix G D L P J Y n cfg hYZ h885 h886 h889
  have hMK := h57 G D L P J Y n cfg h847 h61 h869 hK318 hSch hCat hSLB h885 h887 h888 h889
    hF hSzK
  have h9 := hY12 G D L P J Y n cfg hYZ h885 h886 h887 h888 h889
  have he : evenRank G = 3 := (h885 L P hset).2.2
  have hKY : perfInter890 J (centralizer (Y : Set G)) ≤ normalizer (Y : Set G) := fun k hk => by
    obtain ⟨k', -, rfl⟩ := hk
    exact Subgroup.centralizer_le_normalizer _ k'.2.2
  have hO := h5e1 G _ n hperf hO2 hn3 hnodd hSzK
    (fun p hp hp2 T _ hT hT2 => by
      have := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2
        (normalizer (T : Set G)) ⟨T, hT, hT2, rfl⟩
      omega)
    _ hKY
  exact r890_theorem5e3 G D L P J Y n cfg hMK
    (h5e2 hSch hCat hSLB G D L P J Y n cfg h885 h9 hF hSzK hO)

theorem r890_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G)
    (h847 : UC22.R847ThinNe3 D) (h61 : UC6.R6_1 D) (h869 : F08.R869 D) (h856 : R856 D)
    (h881 : R881 D)
    (h882 : R882 D) (h885 : R885 D) (h886 : R886 D) (h887 : R887 D) (h888 : R888 D)
    (h889 : R889 D) (hJ2 : J2NotSL3PiType) (hK318 : UCK.K318) (hSch : UCK.KSch)
    (hCat : PartTwo.Inputs1719.K_CatalogueThreePrimeSz)
    (hSLB : CFSG.RankThree.PartOne.N143.SectionListBound)
    (hJ3 : J2OrderThree_890) (hFix : J2ThreeBFix_890) (hNoFF : J2NoFF_890) (hOff : PUJ2Offender_890)
    (hCore : PUJ2Core_890) (h410 : PartTwo.Inputs1719.UC1_4_10) (h5e2 : Lemma5e2_890)
    (h11 : Lemma1_1_890) (h22 : Prop2_2_890) (h31 : Lemma3_1_890) (h32 : Lemma3_2a_890)
    (h3B : Y3B_890) (hQ : QuasiOfFstarNe_890) (h2c : Step2Comm_890)
    (hCh : ChiefFactorExists_890) (h5 : Step5_890) (h6 : Step6_890) (h5b1 : Lemma5b1_890)
    (hSyl : Lemma5b1Syl_890) (h41 : Lemma41_890) (h42 : Lemma42_890) (hSet : PUSetup_890)
    (hNorm : PUNormalizer_890)
    (h5e1 : Lemma5e1_890) (hY12 : J2OrderThree_890 → Y3B_890 → Y12_890) : R890 D :=
  r890_of_lanes D h11 r890_lnormal h22
    (r890_prop3_5_of_leaves h31 h32 h3B hJ3 hQ h2c hCh h5 h6)
    (r890_theorem5d7_of_uc410
      (r890_pairStep_of_leaves h31 h32 h5b1 hSyl h41 h42 hSet hCore hNoFF hOff
        hNorm)
      h31 h32 h410)
    (hY12 hJ3 h3B) h5e1 h5e2 hFix hK318 hSch hCat hSLB h847 h61 h869
    h856 h881 h882 h885 h886 h887 h888 h889 hJ2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
