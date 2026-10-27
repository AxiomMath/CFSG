module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5L
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09e
import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.GroupTheory.PElementSubgroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.Quasithin.Background.B1Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {G : Type} [Group G] [Finite G]

theorem charTwo_of_fstar {H : Subgroup G} (hF : Fstar H = pCoreOf 2 H) :
    CFSG.QuasithinUnique.CharTwo H := by
  rintro y ⟨hyH, hyc⟩
  have hc : (⟨y, hyH⟩ : ↥H) ∈ centralizer (CFSG.Open.genFittingFStar ↥H : Set ↥H) := by
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 H := by
      rw [← hF]
      exact mem_map_of_mem _ hw
    exact Subtype.ext ((mem_centralizer_iff.1 hyc) _ hw')
  rw [← hF]
  exact mem_map_of_mem H.subtype (CFSG.Adapters.generalized_fitting_self_centralizing ↥H hc)

variable {Y H S : Subgroup G}

local notation "V₀" => conjClosure (omegaOneCenterOf S) (L9 Y H ⊔ S)

theorem le_L9_sup {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S) : Y ≤ L9 Y H ⊔ S :=
  le_of_le_of_isSylowOf ((opp_le_L9 Y H).trans le_sup_left) le_sup_right hY.2.2.2
    hY.2.1.1.2.2.2.2

theorem isTwoReducedIn_conjClosure_L9 {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S)
    (hSH : IsSylowOf 2 S H) : IsTwoReducedIn (L9 Y H ⊔ S) V₀ ∧ V₀ ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L9 Y H ≤ H := L9_le_of_le hY.1.2.1.1
  obtain ⟨hSG, hS2, hodd⟩ := isSylowOf_iff.1 (hSH.of_le le_sup_right (sup_le hLH hSH.le))
  have hF : CFSG.QuasithinUnique.CharTwo (L9 Y H ⊔ S) :=
    ((charTwo_of_fstar hY.2.2.1.2).of_normal hLH ((normal_subgroupOf_iff_le_normalizer hLH).2
      (le_normalizer_L9 Y H))).sup_of_le_normalizer hS2 (hSH.le.trans (le_normalizer_L9 Y H))
  refine ⟨isTwoReducedIn_conjClosure_of_sylowIn hSG hS2 hodd hF le_rfl, ?_⟩
  exact (conjClosure_le_centerOf_pCoreOf_of_sylowIn hSG hS2 hodd hF le_rfl).1.trans
    (inf_le_left.trans (pCoreOf_two_le_of_sylowIn hSG hS2 hodd))

theorem not_L9_le_centralizer {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S)
    (hR : pCoreOf 2 Y ≠ ⊥) (hSM : ¬ IsSylowOf 2 S D.M) :
    ¬ L9 Y H ≤ centralizer (V₀ : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hLC
  obtain ⟨hSY, hS2, hodd⟩ := isSylowOf_iff.1 hY.2.2.2
  have hZS := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S
  have hchar := CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S
  have hS1 : S ≠ ⊥ := by
    intro h
    apply hR
    rw [← le_bot_iff, ← h]
    exact pCoreOf_two_le_of_sylowIn hSY hS2 hodd
  have hLZ : L9 Y H ≤ centralizer (omegaOneCenterOf S : Set G) :=
    hLC.trans (centralizer_le (le_conjClosure _ _))
  have hYZ : Y ≤ normalizer (omegaOneCenterOf S : Set G) :=
    le_of_le_of_isSylowOf ((opp_le_L9 Y H).trans (hLZ.trans (centralizer_le_normalizer _)))
      (le_normalizer.trans (normalizer_le_normalizer_of_char hZS hchar)) hY.2.2.2
      hY.2.1.1.2.2.2.2
  have hNM := normalizer_le_of_hyp97 (r910_holds D) hY hSM hZS
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 hS1) hchar hYZ
  exact hY.1.2.1.2.1 ((eq_L9_sup_of_hyp91 hY.1).trans_le
    (sup_le (hLZ.trans ((centralizer_le_normalizer _).trans hNM)) inf_le_right))

theorem inf_centralizer_le_I9 {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S)
    (hR : pCoreOf 2 Y ≠ ⊥) (hSM : ¬ IsSylowOf 2 S D.M) (hs : IsSimpleGroup (Lbar9 Y H)) :
    L9 Y H ⊓ centralizer (V₀ : Set G) ≤ I9 H := by
  have hLV : L9 Y H ≤ normalizer (V₀ : Set G) :=
    le_sup_left.trans (le_normalizer_conjClosure _ _)
  rcases le_I9_or_le_of_isSimpleGroup hY.1.2.1.1 inf_le_left
    (B2F.le_normalizer_inf le_normalizer (B2F.le_normalizer_centralizer hLV)) hs with h | h
  · exact h
  · exact absurd (h.trans inf_le_right) (not_L9_le_centralizer hY hR hSM)

theorem inf_centralizer_le_of_hyp97 {D : Data G} {D₃ : Subgroup G} (hY : Hyp97 D Y H D₃ S)
    (hA5 : IsAlt (Bar2 (Opp 3 Y)) 5) (hR : pCoreOf 2 Y ≠ ⊥) (hSM : ¬ IsSylowOf 2 S D.M)
    (hs : IsSimpleGroup (Lbar9 Y H)) : Y ⊓ centralizer (V₀ : Set G) ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := Y ⊓ centralizer (V₀ : Set G) with hE
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hYE : Y ≤ normalizer (E : Set G) := B2F.le_normalizer_inf le_normalizer
    (B2F.le_normalizer_centralizer ((le_L9_sup hY).trans (le_normalizer_conjClosure _ _)))
  have hXE : Opp 3 Y ⊓ E ≤ CFSG.Open.pCoreOf 2 (Opp 3 Y) :=
    (le_inf inf_le_left ((le_inf (inf_le_left.trans (opp_le_L9 Y H))
      (inf_le_right.trans inf_le_right)).trans (inf_centralizer_le_I9 hY hR hSM hs))).trans
      (inf_I9_le_pCoreOf le_rfl (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm hA5
        (hXY.trans hY.1.2.1.1))
  obtain ⟨i, hi⟩ :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Opp 3 Y)).to_le hXE).exists_card_eq
  obtain ⟨k, hk⟩ := hY.2.1.1.2.2.2.2
  have hidx : (Opp 3 Y ⊓ E).relIndex E ∣ 2 ^ k := by
    rw [← CFSG.AGLEmbedding.L34FF.relIndex_left_sup
      (inf_le_left.trans (le_normalizer_opp_self 3 Y))]
    exact ⟨_, hk.symm.trans (relIndex_mul_relIndex _ _ Y le_sup_left
      (sup_le hXY inf_le_left)).symm⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx
  have hcard := relIndex_mul_card (Opp 3 Y ⊓ E) E
  rw [inf_of_le_left inf_le_right, hj, hi, ← pow_add] at hcard
  obtain ⟨hSY, hS2, hodd⟩ := isSylowOf_iff.1 hY.2.2.2
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hYE
    (IsPGroup.of_card hcard.symm)).trans (pCoreOf_two_le_of_sylowIn hSY hS2 hodd)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
