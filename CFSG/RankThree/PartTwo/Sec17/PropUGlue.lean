module

public import CFSG.RankThree.PartTwo.Sec17.PropU
public import CFSG.RankThree.PartTwo.Sec17.PropUJ2Gen
public import CFSG.RankThree.PartTwo.Sec17.PropUSetup
public import CFSG.RankThree.PartTwo.Sec17.PropUCover
public import CFSG.RankThree.PartTwo.Sec17.PropULemmaThree
public import CFSG.RankThree.PartTwo.Sec17.PropULemmaFour
public import CFSG.RankThree.PartTwo.Sec17.PropULemmaFive
public import CFSG.RankThree.PartTwo.Sec17.PropUStepTwoC
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec14.Item148StepsNHJ
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

theorem not_three_dvd_card_pPrimeCoreOf {G : Type} [Group G] [Finite G] (F : Subgroup G) :
    ¬ 3 ∣ Nat.card ↥(pPrimeCoreOf 3 F) := by
  have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥F)
  have hcard : Nat.card ↥(pPrimeCoreOf 3 F) = Nat.card ↥(CFSG.pPrimeCore 3 ↥F) :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective (CFSG.pPrimeCore 3 ↥F) F.subtype F.subtype_injective).toEquiv.symm
  rw [hcard]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h

theorem eq_bot_of_isPGroup_three {G : Type} [Group G] [Finite G] {N V : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card N) (hV : IsPGroup 3 V) (hVN : V ≤ N) : V = ⊥ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hV
  have hd : Nat.card V ∣ Nat.card N := Subgroup.card_dvd_of_le hVN
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Subgroup.eq_bot_of_card_eq V (by simpa using hk)
  · exfalso
    apply h3
    rw [hk] at hd
    exact (dvd_pow_self 3 hkpos.ne').trans hd

theorem centralizes_generalizedFitting {G : Type} [Group G] [Finite G] {N₀ X : Subgroup G}
    (hfit : ∀ q : ℕ, q.Prime →
      X ≤ Subgroup.centralizer ((CFSG.Open.pCoreOf q N₀ : Subgroup G) : Set G))
    (hlayer : X ≤ Subgroup.centralizer ((inSubgroup CFSG.layer N₀ : Subgroup G) : Set G)) :
    X ≤ Subgroup.centralizer ((inSubgroup CFSG.generalizedFitting N₀ : Subgroup G) : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  have hF : inSubgroup CFSG.generalizedFitting N₀ =
      (⨆ q : (Nat.card ↥N₀).primeFactors, CFSG.Open.pCoreOf (q : ℕ) N₀) ⊔
        inSubgroup CFSG.layer N₀ := by
    unfold inSubgroup
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup,
      CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup]
    rfl
  rw [hF]
  refine sup_le (iSup_le fun q => ?_) ?_
  · exact Subgroup.le_centralizer_iff.mp (hfit q (Nat.prime_of_mem_primeFactors q.2))
  · exact Subgroup.le_centralizer_iff.mp hlayer

end CFSG.RankThree.PartTwo.Sec17.PropU

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec17.PropU

theorem claim1724DeltaUp_of_inputs
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hbot : Item145BotS17)
    (h148 : Item148HJS14) (h149 : Item149S14) (h152 : Item152R) (h155 : Item155R)
    (hFT : J2NotSectionOfGLFourTwo) (hCover : J2CoverHasElemAbelianEight) :
    Claim1724DeltaUp := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hJ R T hR hR1 hRΛ hT hRT hTN
  classical
  have hs : Sec17Std G A c L Y₀ := h.toSec17Std
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hp : p.Prime := h.p_prime
  have hp3 : 3 < p := h.three_lt_p
  obtain ⟨hΩ, hLcov, -⟩ := rank3II_17_15_HJ_of hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hJ
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    nonempty_quotient_J2 hs hJ hLcov
  have hS14 : Sec14Std G A c L := hs.toSec15R.toSec14Std
  have hAll : AllPointsHJ A := by
    intro e he
    rw [hΩ, Set.mem_singleton_iff] at he
    refine ⟨L, ?_, hJ⟩
    rw [lA_eq_of_zpowers_eq he]
    exact hs.mem_lA
  have h142 : Concl142 A (lB A) := concl142_of_allPointsHJ hS14 hAll
  have h148' : Item148 A (lB A) := h148 G A c L hS14 hAll
  have h149' : Item149 A (lB A) := h149 G A c L hS14
  have h152' : Item152 A (lB A) := h152 G A c L hs.toSec15R
  have h155' : Item155 A (lB A) := h155 G A c L hs.toSec15R
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L Y₀ hs
  have hTp : IsPGroup p T := isPGroup_of_mem_scriptQPi hp hT
  have hRp : IsPGroup p R := isPGroup_of_mem_scriptQPi hp hR
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR.1.1.1.2.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.1.1.1.2.2
  obtain ⟨Rs, hRsR, hRs1, hTRs, hARs⟩ := exists_Rstar hp hTp hRT hTN hR1 hAR hAT
  have hRsp : IsPGroup p Rs := hRp.to_le hRsR
  have hK : Subgroup.normalizer (Rs : Set G) ∈ scriptY A :=
    normalizer_mem_scriptY hG hp hRsp hRs1 hARs
  set K : Subgroup G := Subgroup.normalizer (Rs : Set G) with hKdef
  have hAK : A ≤ K := hARs
  have hTK : T ≤ K := hTRs.trans (Subgroup.centralizer_le_normalizer _)
  have hAY : A ≤ Subgroup.normalizer (Y₀ : Set G) := hs.le_normalizer_y0
  have hAC : A ≤ Subgroup.normalizer ((Y₀ ⊓ Subgroup.centralizer (Rs : Set G) : Subgroup G) :
      Set G) := pu_le_normalizer_inf hAY (le_normalizer_centralizer_of hARs)
  have hCY : Y₀ ⊓ Subgroup.centralizer (Rs : Set G) ≤ Y₀ := inf_le_left
  have hcov : Y₀ = (Y₀ ⊓ Subgroup.centralizer (Rs : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    refine le_antisymm ?_ (sup_le hCY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀))
    calc Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := hRΛ
      _ ≤ _ := sup_le_sup_right (inf_le_inf_left Y₀ (Subgroup.centralizer_le hRsR)) _
  obtain ⟨X, hXC, hAX, hXcov, hX4, hXV, hXJ⟩ :=
    exists_covering_Y4 PropU.J2Gen.j2GenByTwoSubgroups hs hJ hLcov h142 hCY hAC hcov
  have hXY : X ≤ Y₀ := hXC.trans hCY
  have hXK : X ≤ K := hXC.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨hKF, hXF, hFcard, hXN⟩ :=
    lemma33 hs hJ hYJ hbot' h148' h149' hX4 hXJ hK hXK
  set F : Subgroup G := oPrimeResidualOf 3 (delta A (lB A) K) with hFdef
  set N₀ : Subgroup G := pPrimeCoreOf 3 F with hN₀def
  by_cases hO2 : CFSG.Open.pCoreOf 2 N₀ = ⊥
  ·
    have hFK : F ≤ K := (oPrimeResidualOf_le_self 3 _).trans (delta_le K)
    have hN₀F : N₀ ≤ F := Subgroup.map_subtype_le _
    have hN₀top : N₀ ≠ ⊤ := fun htop => hK.1 (eq_top_iff.mpr (htop.symm.le.trans (hN₀F.trans hFK)))
    have hKG : CFSG.IsKGroup ↥N₀ := (hG.sectionFourHyp hN₀top).kGroup
    have h3 : ¬ 3 ∣ Nat.card N₀ := not_three_dvd_card_pPrimeCoreOf F
    have hloc5 : CFSG.Assembly.RankThreeEven.localRank 5 G < 3 :=
      hG.localRank_lt 5 Nat.prime_five (by norm_num)
    have hFN₀ : F ≤ Subgroup.normalizer (N₀ : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_pPrimeCoreOf 3 F)
    have hXN₀ : X ≤ Subgroup.normalizer (N₀ : Set G) := hXF.trans hFN₀
    have hX3 : oPrimeResidualOf 3 X = X := hX4.2.1.symm
    have hlayer := pe_layer hloc5 hKG h3 hXN₀ hX3 hXJ
    have hfit : ∀ q : ℕ, q.Prime →
        X ≤ Subgroup.centralizer ((CFSG.Open.pCoreOf q N₀ : Subgroup G) : Set G) := by
      intro q hq
      haveI : Fact q.Prime := ⟨hq⟩
      by_cases hq5 : 5 ≤ q
      · exact pf hFT hCover hq hq5 (hG.localRank_lt q hq (by omega))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup q N₀)
          (hXN₀.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q N₀)) hX3 hXJ
      · have hq23 : q = 2 ∨ q = 3 := by
          have h2 := hq.two_le
          interval_cases q
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hq (by decide)
        have hbotcent : ∀ V : Subgroup G, V = ⊥ →
            X ≤ Subgroup.centralizer ((V : Subgroup G) : Set G) := by
          rintro V rfl x -
          refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
          rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
          subst hy
          simp
        rcases hq23 with rfl | rfl
        · exact hbotcent _ hO2
        · exact hbotcent _ (eq_bot_of_isPGroup_three h3
            (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 N₀)
            (CFSG.LieType.BorelTits.pCoreOf_le 3 N₀))
    have hcent := centralizes_generalizedFitting hfit hlayer
    obtain ⟨hXO2, hKX⟩ := step3 hKF hFcard hXF hXJ hXN hO2 hcent
    have hXV' : X ⊓ CFSG.Open.pCoreOf 2 Y₀ = ⊥ := hXV.symm.trans hXO2
    have hTcent : T ≤ Subgroup.centralizer (X : Set G) :=
      step4 hs hJ hYJ hp hp3 hXY hXV' hXcov hAX hAT (hTK.trans hKX) hTp
    refine le_antisymm ?_ (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀))
    calc Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀ := hXcov
      _ ≤ _ := sup_le_sup_right (le_inf hXY (Subgroup.le_centralizer_iff.mp hTcent)) _
  ·
    have hKN : K ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 N₀ : Subgroup G) : Set G) :=
      hKF.trans ((normalizer_le_normalizer_pPrimeCoreOf 3 F).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N₀))
    have hN2 : CFSG.Assembly.IsTwoLocal
        (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 N₀ : Subgroup G) : Set G)) :=
      ⟨CFSG.Open.pCoreOf 2 N₀, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N₀, rfl⟩
    have hΔ := delta_le_normalizer_of_twoLocal hG hG.charTwoType h152' h155' hs.y0Star_eq hX4 hXY
      hXcov hN2 (hAK.trans hKN) (hXK.trans hKN)
    have hTM : T ≤ Subgroup.normalizer (Y₀ : Set G) :=
      (le_delta hT.1.1 (hTK.trans hKN)).trans hΔ
    exact Proof1723N.covers_of_le_M h1514 hMeets h hJ hTp hTM hAT

section Corollaries

variable
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hbot : Item145BotS17)
    (h148 : Item148HJS14) (h149 : Item149S14) (h152 : Item152R) (h155 : Item155R)
    (hFT : J2NotSectionOfGLFourTwo) (hCover : J2CoverHasElemAbelianEight)

include h1514 hMeets hbot h148 h149 h152 h155 hFT hCover

theorem claim1724DeltaNorm_of_inputs : Claim1724DeltaNorm :=
  claim1724DeltaNorm_of_up
    (claim1724DeltaUp_of_inputs h1514 hMeets hbot h148 h149 h152 h155 hFT hCover)

theorem claim1724DeltaMax_of_inputs : Claim1724DeltaMax :=
  claim1724DeltaMax_of_norm h1514 hMeets
    (claim1724DeltaNorm_of_inputs h1514 hMeets hbot h148 h149 h152 h155 hFT hCover)

end Corollaries

end CFSG.RankThree.PartTwo.Sec17
