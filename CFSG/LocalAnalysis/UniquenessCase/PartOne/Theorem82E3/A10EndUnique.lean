module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKey
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPushUp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTrichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndGamma
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndNineSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPushUpCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarCore
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.Goldschmidt75.Sig32
import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {c : Ctx82E3 D}

theorem le_relPPrimeCore_of_balance (F : A10Frame c) (hF : A10Facts F)
    (hStar : KFactE27Signalizer) {Q : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M)
    (hAQ : F.A ≤ Q) {H : Subgroup G} (hHtop : H ≠ ⊤) (hQH : Q ≤ H)
    (hbal : ∀ a ∈ F.A, a ≠ 1 → ∀ W : Subgroup G,
      W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
      F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G)))
    {W : Subgroup G} (hWH : W ≤ H) (hAW : F.A ≤ Subgroup.normalizer (W : Set G))
    (hW : Nat.Coprime (Nat.card W) 3) : W ≤ CFSG.Open.relPPrimeCore 3 H := by
  have hAH : F.A ≤ H := hAQ.trans hQH
  refine A10Gen.le_relPPrimeCore_of_subgroupOf_le hWH ?_
  have hHyp : UC22.InS3.UC327.Hyp327 ↥H (Q.subgroupOf H) (F.A.subgroupOf H) :=
    A10Gen.hyp327_subgroupOf (G := G) D.standing.kProper
      (F.isSylowOf_top_of_isSylowOf hF hQ) (F.nonempty_mulEquiv_zwr hQ)
      F.elemAbelian F.card_A hAQ hHtop hQH
  have hZwr : Nonempty (↥(Q.subgroupOf H) ≃* UC22.InS3.UC326.ZWr 1) :=
    A10Gen.nonempty_mulEquiv_zwr_subgroupOf (F.nonempty_mulEquiv_zwr hQ) hQH
  have hbalH := A10Gen.balance_subgroupOf (A := F.A) (H := H) hAH hbal
  have hAW' : F.A.subgroupOf H ≤
      Subgroup.normalizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hAW (Subgroup.mem_subgroupOf.mp hm)) (w : G)).mp hw
  have hWcop : Nat.Coprime (Nat.card ↥(W.subgroupOf H)) 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv]
    exact hW
  exact A10Gen.le_pPrimeCore_of_kFactE27Signalizer hStar (D.standing.kProper.isKGroup H hHtop)
    hHyp hZwr hbalH hAW' hWcop

private theorem exists_maximal_bad {Q R : Subgroup G} (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥)
    (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hbad : ¬ Theorem82.UniqueTwoLocal D.M (Q ⊔ R)) :
    ∃ R₀ : Subgroup G, IsPGroup 2 R₀ ∧ R₀ ≠ ⊥ ∧ Q ≤ Subgroup.normalizer (R₀ : Set G) ∧
      ¬ Theorem82.UniqueTwoLocal D.M (Q ⊔ R₀) ∧
      ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → Q ≤ Subgroup.normalizer (T : Set G) →
        Nat.card R₀ < Nat.card T → Theorem82.UniqueTwoLocal D.M (Q ⊔ T) := by
  classical
  let bad : Set (Subgroup G) := {S | IsPGroup 2 S ∧ S ≠ ⊥ ∧
    Q ≤ Subgroup.normalizer (S : Set G) ∧ ¬ Theorem82.UniqueTwoLocal D.M (Q ⊔ S)}
  have hne : bad.Nonempty := ⟨R, hR2, hR, hQR, hbad⟩
  have hfin : bad.Finite := Set.toFinite bad
  obtain ⟨R₀, hmax⟩ := hfin.exists_maximalFor (fun S : Subgroup G => Nat.card ↥S) bad hne
  obtain ⟨hR₀2, hR₀ne, hQR₀, hbad₀⟩ := hmax.prop
  refine ⟨R₀, hR₀2, hR₀ne, hQR₀, hbad₀, fun T hT2 hTne hQT hlt => ?_⟩
  by_contra hTbad
  exact absurd (hmax.le ⟨hT2, hTne, hQT, hTbad⟩) (not_le.mpr hlt)

private theorem calCGS_le_of_eq
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {Q R C S : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) (hQA : F.A ≤ Q)
    (hQR : Q ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R)
    (hNC2 : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)))
    (hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G))
    (hmaxle : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      Q ≤ Subgroup.normalizer (S' : Set G) → R ≤ S' → Nat.card S' ≤ Nat.card S)
    (hSeq : S = R) : Subgroup.normalizer (C : Set G) ≤ D.M := by
  have hRM : R ≤ D.M := F.le_M_of_isPGroup_two hF hC hR2 (hQA.trans hQR)
  have hMO2 : D.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    c.le_normalizer_L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hO2M : CFSG.Open.pCoreOf 2 c.L ≤ D.M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L).trans c.hyp81.1
  have hO22 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 c.L
  have hsup2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 c.L ⊔ R) :=
    hO22.to_sup_of_normal_left' hR2 (hRM.trans hMO2)
  have hQsup : Q ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 c.L ⊔ R : Subgroup G) : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_sup (N := Q) (A := CFSG.Open.pCoreOf 2 c.L) (B := R)
      (hQ.le.trans hMO2) hQR
  have hcardle : Nat.card ↥(CFSG.Open.pCoreOf 2 c.L ⊔ R) ≤ Nat.card ↥S :=
    hmaxle (CFSG.Open.pCoreOf 2 c.L ⊔ R) (sup_le hO2M hRM) hsup2 hQsup le_sup_right
  rw [hSeq] at hcardle
  have hEq : CFSG.Open.pCoreOf 2 c.L ⊔ R = R :=
    (Subgroup.eq_of_le_of_card_ge (H := R) (K := CFSG.Open.pCoreOf 2 c.L ⊔ R)
      le_sup_right hcardle).symm
  have hO2R : CFSG.Open.pCoreOf 2 c.L ≤ R := le_sup_left.trans (le_of_eq hEq)
  have hRphi : (R.subgroupOf D.M).map F.phiA = ⊥ := F.map_phiA_eq_bot hQ hQA hRM hR2 hQR
  have hLR : c.L ≤ Subgroup.normalizer (R : Set G) := F.L_le_normalizer hRM hRphi hO2R
  exact F.le_M_of_L_le hNC2 (hLR.trans hNRC)

private theorem calCGS_le_of_lt {Q R C S : Subgroup G}
    (hQR : Q ≤ Subgroup.normalizer (R : Set G)) (hR : R ≠ ⊥)
    (hNC2 : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)))
    (hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G))
    (hS2 : IsPGroup 2 S) (hQS : Q ≤ Subgroup.normalizer (S : Set G)) (hlt : R < S)
    (hgood : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ →
      Q ≤ Subgroup.normalizer (T : Set G) → Nat.card R < Nat.card T →
      Theorem82.UniqueTwoLocal D.M (Q ⊔ T)) :
    Subgroup.normalizer (C : Set G) ≤ D.M := by
  have hltT : R < S ⊓ Subgroup.normalizer (R : Set G) :=
    CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) hS2 hlt
  have hTne : S ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ :=
    fun hbot => hR (le_bot_iff.mp (hbot ▸ le_of_lt hltT))
  have hQT : Q ≤ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) :
      Set G) :=
    CFSG.Goldschmidt75.le_normalizer_inf_of_le hQS (hQR.trans Subgroup.le_normalizer)
  have huniq := hgood _ (hS2.to_le inf_le_left) hTne hQT (Subgroup.card_lt_of_lt hltT)
  have hle : Q ⊔ (S ⊓ Subgroup.normalizer (R : Set G)) ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (hQR.trans hNRC) (inf_le_right.trans hNRC)
  exact huniq _ hNC2 hle

private theorem calCGS_le
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {Q R : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M)
    (hQA : F.A ≤ Q) (hQR : Q ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R)
    (hR : R ≠ ⊥)
    (hgood : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → Q ≤ Subgroup.normalizer (T : Set G) →
      Nat.card R < Nat.card T → Theorem82.UniqueTwoLocal D.M (Q ⊔ T)) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS R ≤ D.M := by
  classical
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS]
  refine iSup_le fun C => iSup_le fun hCne => iSup_le fun hCR => iSup_le fun hCchar => ?_
  have hNC2 : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hCne, hR2.to_le hCR, rfl⟩
  have hNRC : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
      hCR hCchar
  let family : Set (Subgroup G) := {S | S ≤ D.M ∧ IsPGroup 2 S ∧
    Q ≤ Subgroup.normalizer (S : Set G) ∧ R ≤ S}
  have hfamne : family.Nonempty :=
    ⟨R, F.le_M_of_isPGroup_two hF hC hR2 (hQA.trans hQR), hR2, hQR, le_rfl⟩
  have hfamfin : family.Finite := Set.toFinite family
  obtain ⟨S, hSmax⟩ :=
    hfamfin.exists_maximalFor (fun S : Subgroup G => Nat.card ↥S) family hfamne
  obtain ⟨-, hS2, hQS, hRS⟩ := hSmax.prop
  have hmaxle : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      Q ≤ Subgroup.normalizer (S' : Set G) → R ≤ S' → Nat.card S' ≤ Nat.card S :=
    fun S' h1 h2 h3 h4 => hSmax.le ⟨h1, h2, h3, h4⟩
  by_cases hSeq : S = R
  · exact calCGS_le_of_eq F hF hC hQ hQA hQR hR2 hNC2 hNRC hmaxle hSeq
  · exact calCGS_le_of_lt hQR hR hNC2 hNRC hS2 hQS
      (lt_of_le_of_ne hRS (fun h => hSeq h.symm)) hgood

private theorem balance_of_trichotomy (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {Q N : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) (hAQ : F.A ≤ Q)
    (hQN : Q ≤ N) (hN : CFSG.Open.IsTwoLocal N) (hNM : ¬ N ≤ D.M) :
    ∀ a ∈ F.A, a ≠ 1 → ∀ W : Subgroup G,
      W ≤ N ⊓ Subgroup.centralizer ({a} : Set G) →
      F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (N ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hAN : F.A ≤ N := hAQ.trans hQN
  rcases F.trichotomy hF hC hN hAN with h | hNM' | ⟨hSyl, -⟩
  · exact h
  · exact absurd hNM' hNM
  · exfalso
    have hQeq : Q = F.A := hSyl.eq_of_le hAQ hQN hQ.isPGroup
    have hQ81 : Nat.card ↥Q = 81 := by
      obtain ⟨e⟩ := F.nonempty_mulEquiv_zwr hQ
      calc Nat.card ↥Q = Nat.card (UC326.ZWr 1) := Nat.card_congr e.toEquiv
        _ = 81 := by
          simpa using (UC326.zwr_card_center_Zwr (n := 1) (by norm_num)).1
    rw [hQeq, F.card_A] at hQ81
    norm_num at hQ81

private theorem le_of_isPGroup_normalized {Q R N : Subgroup G} (hR2 : IsPGroup 2 R)
    (hR : R ≠ ⊥) (hQN : Q ≤ N) (hRN : R ≤ N) (hN : CFSG.Open.IsTwoLocal N)
    (hNM : ¬ N ≤ D.M) (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hgood : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ →
      Q ≤ Subgroup.normalizer (T : Set G) → Nat.card R < Nat.card T →
      Theorem82.UniqueTwoLocal D.M (Q ⊔ T)) :
    ∀ T : Subgroup G, T ≤ N → IsPGroup 2 T →
      Q ≤ Subgroup.normalizer (T : Set G) → R ≤ Subgroup.normalizer (T : Set G) → T ≤ R := by
  intro T hTN hT2 hQT hRT
  by_contra hTR
  have hsup2 : IsPGroup 2 ↥(R ⊔ T) := hR2.to_sup_of_normal_right' hT2 hRT
  have hsupne : R ⊔ T ≠ ⊥ := fun hbot => hR (le_bot_iff.mp (hbot ▸ le_sup_left))
  have hQsup : Q ≤ Subgroup.normalizer ((R ⊔ T : Subgroup G) : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_sup (N := Q) (A := R) (B := T) hQR hQT
  have hcard : Nat.card R < Nat.card ↥(R ⊔ T) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left (fun h => hTR (h ▸ le_sup_right)))
  exact hNM (hgood _ hsup2 hsupne hQsup hcard N hN (sup_le hQN (sup_le hRN hTN)))

private theorem false_of_maximal_bad
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hStar : KFactE27Signalizer) (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    {Q R : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) (hAQ : F.A ≤ Q)
    (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) (hQR : Q ≤ Subgroup.normalizer (R : Set G))
    (hbad : ¬ Theorem82.UniqueTwoLocal D.M (Q ⊔ R))
    (hgood : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ →
      Q ≤ Subgroup.normalizer (T : Set G) → Nat.card R < Nat.card T →
      Theorem82.UniqueTwoLocal D.M (Q ⊔ T)) : False := by
  classical
  have hNex : ∃ N : Subgroup G, CFSG.Open.IsTwoLocal N ∧ Q ⊔ R ≤ N ∧ ¬ N ≤ D.M := by
    by_contra hcon
    refine hbad fun H hH hQH => ?_
    by_contra hHM
    exact hcon ⟨H, hH, hQH, hHM⟩
  obtain ⟨N, hN, hQRN, hNM⟩ := hNex
  have hQN : Q ≤ N := le_trans le_sup_left hQRN
  have hRN : R ≤ N := le_trans le_sup_right hQRN
  have hNtop : N ≠ ⊤ := by
    intro htop
    have htop2 : CFSG.Open.IsTwoLocal (⊤ : Subgroup G) := htop ▸ hN
    exact hNM (htop ▸ F.le_M_of_L_le htop2 le_top)
  have hbal := balance_of_trichotomy F hF hC hQ hAQ hQN hN hNM
  have hRcop : Nat.Coprime (Nat.card R) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) hR2 Nat.prime_three
        (by norm_num))).symm
  have hRK : R ≤ CFSG.Open.relPPrimeCore 3 N :=
    F.le_relPPrimeCore_of_balance hF hStar hQ hAQ hNtop hQN hbal hRN
      (hAQ.trans hQR) hRcop
  have hmax := le_of_isPGroup_normalized hR2 hR hQN hRN hN hNM hQR hgood
  refine hNM (A10Gen.le_of_calCGS_le hKPSz D.standing.kProper ?_ hQ.isPGroup hQN hR2 hR hQR hRK
    (D.standing.charTwo N hN) hmax (calCGS_le F hF hC hQ hAQ hQR hR2 hR hgood))
  have hdvd : Nat.card F.A ∣ Nat.card G := Subgroup.card_subgroup_dvd_card F.A
  rw [F.card_A] at hdvd
  exact dvd_trans (by norm_num : 3 ∣ 27) hdvd

theorem uniqueTwoLocal_sup
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hStar : KFactE27Signalizer) (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    {Q : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) (hAQ : F.A ≤ Q)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥)
    (hQR : Q ≤ Subgroup.normalizer (R : Set G)) :
    Theorem82.UniqueTwoLocal D.M (Q ⊔ R) := by
  by_contra hbad
  obtain ⟨R₀, hR₀2, hR₀ne, hQR₀, hbad₀, hgood⟩ :=
    exists_maximal_bad (D := D) hR2 hR hQR hbad
  exact false_of_maximal_bad F hF hC hStar hKPSz hQ hAQ hR₀2 hR₀ne hQR₀ hbad₀ hgood

theorem centralizer_le_of_pCoreOf_ne_bot
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hStar : KFactE27Signalizer) (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) ≠ ⊥) :
    Subgroup.centralizer (B : Set G) ≤ D.M := by
  classical
  obtain ⟨P', hP', hAP', hP'C⟩ := F.exists_isSylowOf_le_centralizer hBA hB3 hB9
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 C) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 C
  have hCRC : C ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C)
  have hP'R : P' ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G) := hP'C.trans hCRC
  have huniq := uniqueTwoLocal_sup F hF hC hStar hKPSz hP' hAP' hR2 hO hP'R
  have hNle : Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G) ≤ D.M :=
    huniq (Subgroup.normalizer (CFSG.Open.pCoreOf 2 C : Set G))
      ⟨CFSG.Open.pCoreOf 2 C, hO, hR2, rfl⟩ (sup_le hP'R Subgroup.le_normalizer)
  exact hCRC.trans hNle

theorem exists_pCoreOf_centralizer_eq_bot
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hStar : KFactE27Signalizer) (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) :
    ∃ B ≤ F.A, Nat.card B = 3 ∧ F.deg B = 9 ∧
      ¬ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) ≤ D.M ∧
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥ := by
  obtain ⟨B, hBA, hB3, hB9, hnot⟩ :=
    F.exists_relPPrimeCore_not_le hF (fun B hB h3 _ => hC B hB h3)
  refine ⟨B, hBA, hB3, hB9, hnot, ?_⟩
  by_contra hO
  refine hnot (le_trans ?_ (centralizer_le_of_pCoreOf_ne_bot F hF hC hStar hKPSz hBA hB3 hB9 hO))
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
    (Subgroup.centralizer (B : Set G))

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
