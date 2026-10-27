module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.SectionRank
open CFSG.LocalAnalysis.UniquenessCase.UC22

local notation "pRank" => CFSG.Open.pRank
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_of_centralizing_mod_pCore {L H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : center (Bar2 L) = ⊥) (hHN : H ≤ normalizer (L : Set G)) {y z : G}
    (hyH : y ∈ H) (hzH : z ∈ H) (hyL : y ∈ L) (hy : orderOf y = p) (hz : orderOf z = p)
    (hzc : ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : 2 ≤ pRank p H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hconj : Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) :=
    CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hZ
  have hrhz : rhoL L ⟨z, hHN hzH⟩ = 1 := by
    ext w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
    rw [MulAut.one_apply]
    rw [rhoL_fix_iff L ⟨z, hHN hzH⟩ l]
    exact hzc l l.2
  have hbar : ∀ (w : G) (hw : w ∈ L),
      rhoL L ⟨w, Subgroup.le_normalizer hw⟩ = 1 → w ∈ pCoreOf 2 L := by
    intro w hw hrho
    have hconjw : MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : Bar2 L) = 1 := by
      rw [← rhoL_inner L w hw]
      exact hrho
    have h1 : (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : Bar2 L) = 1 :=
      hconj (by rw [hconjw, map_one])
    exact Subgroup.mem_map.mpr ⟨⟨w, hw⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  have hznotO : z ∉ pCoreOf 2 L := by
    intro hzO
    have hzord : IsPGroup p (Subgroup.zpowers z) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [pow_one, Nat.card_zpowers, hz]
    have hz1 : z = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
        hp hp2 hzord (isPGroup_pCoreOf L) (Subgroup.mem_zpowers z) hzO
    rw [hz1, orderOf_one] at hz
    exact hp.ne_one hz.symm
  have hynotO : y ∉ pCoreOf 2 L := by
    intro hyO
    have hyord : IsPGroup p (Subgroup.zpowers y) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [pow_one, Nat.card_zpowers, hy]
    have hy1 : y = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
        hp hp2 hyord (isPGroup_pCoreOf L) (Subgroup.mem_zpowers y) hyO
    rw [hy1, orderOf_one] at hy
    exact hp.ne_one hy.symm
  let K : Subgroup G := Subgroup.zpowers y ⊔ Subgroup.zpowers z
  have hyK : y ∈ K := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hzK : z ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hKH : K ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr hyH) (Subgroup.zpowers_le.mpr hzH)
  let N : Subgroup G := K ⊓ pCoreOf 2 L
  let N' : Subgroup ↥K := N.subgroupOf K
  have hNleK : N ≤ K := inf_le_left
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) := by
    have hKp : K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      hKH.trans (hHN.trans (normalizer_le_normalizer_pCoreOf L))
    exact (le_inf (Subgroup.le_normalizer) hKp).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNleK).mpr hNnorm
  have hNcard : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleK).toEquiv
  have hNp : IsPGroup 2 N := (isPGroup_pCoreOf L).to_le inf_le_right
  have hcopN : ¬ p ∣ Nat.card N' := by
    rw [hNcard]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hNp hp hp2
  have hzL_of_mem : z ∈ Subgroup.zpowers y → z ∈ L := fun hzy =>
    Subgroup.zpowers_le.mpr hyL hzy
  have hrhzL : ∀ (hzL : z ∈ L),
      rhoL L ⟨z, Subgroup.le_normalizer hzL⟩ = 1 := by
    intro hzL
    simpa [show (⟨z, hHN hzH⟩ : ↥(normalizer (L : Set G))) =
        ⟨z, Subgroup.le_normalizer hzL⟩ from Subtype.ext rfl] using hrhz
  have hzy : z ∉ Subgroup.zpowers y := by
    intro hzy
    exact hznotO (hbar z (hzL_of_mem hzy) (hrhzL (hzL_of_mem hzy)))
  have hyz : y ∉ Subgroup.zpowers z := by
    intro hyzmem
    have hcardy : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy]
    have hcardz : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
    have heq : Subgroup.zpowers y = Subgroup.zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyzmem) ?_
      rw [hcardy, hcardz]
    have hymem : y ∈ Subgroup.zpowers z := by
      rw [← heq]
      exact Subgroup.mem_zpowers y
    have hzL : z ∈ L := by
      have hzmem : z ∈ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact Subgroup.zpowers_le.mpr hyL hzmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hymem
    have hpow : (⟨y, Subgroup.le_normalizer hyL⟩ : ↥(normalizer (L : Set G))) =
        (⟨z, Subgroup.le_normalizer hzL⟩ : ↥(normalizer (L : Set G))) ^ n := by
      ext
      show y = z ^ n
      rw [← hn]
    have hrhoy : rhoL L ⟨y, Subgroup.le_normalizer hyL⟩ = 1 := by
      rw [hpow, map_zpow, hrhzL hzL, one_zpow]
    exact hynotO (hbar y hyL hrhoy)
  let qy : ↥K ⧸ N' := QuotientGroup.mk ⟨y, hyK⟩
  let qz : ↥K ⧸ N' := QuotientGroup.mk ⟨z, hzK⟩
  have hqy_ne : qy ≠ 1 := by
    intro h
    have hyN : y ∈ N :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨y, hyK⟩ : ↥K)).mp h)
    exact hynotO hyN.2
  have hqz_ne : qz ≠ 1 := by
    intro h
    have hzN : z ∈ N :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨z, hzK⟩ : ↥K)).mp h)
    exact hznotO hzN.2
  have hqy : orderOf qy = p := by
    have hdvd : orderOf qy ∣ p := by
      have h := orderOf_map_dvd (QuotientGroup.mk' N') (⟨y, hyK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk y hyK, hy] at h
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hqy_ne
    · exact h2
  have hqz : orderOf qz = p := by
    have hdvd : orderOf qz ∣ p := by
      have h := orderOf_map_dvd (QuotientGroup.mk' N') (⟨z, hzK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk z hzK, hz] at h
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hqz_ne
    · exact h2
  have hcommK : ⁅y, z⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hyK hzK) (K.inv_mem hyK)) (K.inv_mem hzK)
  have hcommP : ⁅y, z⁆ ∈ pCoreOf 2 L := by
    have h1 : (⁅z, y⁆)⁻¹ ∈ pCoreOf 2 L :=
      (pCoreOf 2 L).inv_mem (by rw [commutatorElement_def]; exact hzc y hyL)
    have h2 : ⁅y, z⁆ = (⁅z, y⁆)⁻¹ := by
      rw [← commutatorElement_inv (g₁ := y) (g₂ := z), inv_inv]
    rwa [h2]
  have hcommq : qy * qz = qz * qy := by
    show (QuotientGroup.mk' N') ((⟨y, hyK⟩ : ↥K) * (⟨z, hzK⟩ : ↥K)) =
      (QuotientGroup.mk' N') ((⟨z, hzK⟩ : ↥K) * (⟨y, hyK⟩ : ↥K))
    have hdiv : (((⟨y, hyK⟩ : ↥K) * (⟨z, hzK⟩ : ↥K)) *
        ((⟨z, hzK⟩ : ↥K) * (⟨y, hyK⟩ : ↥K))⁻¹ : ↥K) = ⟨⁅y, z⁆, hcommK⟩ := by
      apply Subtype.ext
      show (y * z) * (z * y)⁻¹ = ⁅y, z⁆
      rw [commutatorElement_def]
      group
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    rw [div_eq_mul_inv, hdiv, Subgroup.mem_subgroupOf]
    exact ⟨hcommK, hcommP⟩
  have hindep : qz ∉ Subgroup.zpowers qy := by
    intro hqzy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hqzy
    have hn' : (QuotientGroup.mk' N') (⟨y, hyK⟩ ^ n) = qz := by
      rw [map_zpow]
      exact hn
    have hmem : (⟨y, hyK⟩ ^ n) / ⟨z, hzK⟩ ∈ N' :=
      (QuotientGroup.eq_iff_div_mem).mp hn'
    have hmemP : (((⟨y, hyK⟩ ^ n) / ⟨z, hzK⟩ : ↥K) : G) ∈ pCoreOf 2 L :=
      (Subgroup.mem_subgroupOf.mp hmem).2
    have hval : (((⟨y, hyK⟩ ^ n) / ⟨z, hzK⟩ : ↥K) : G) = y ^ n * z⁻¹ := by
      simp [div_eq_mul_inv]
    have hzL : z ∈ L := by
      have hprod : y ^ n * z⁻¹ ∈ L := by
        rw [← hval]
        exact (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hmemP
      have hyLn : y ^ n ∈ L := L.zpow_mem hyL n
      have hzinv : z⁻¹ ∈ L := by
        have h := L.mul_mem (L.inv_mem hyLn) hprod
        simpa [mul_assoc] using h
      simpa using L.inv_mem hzinv
    have hrhz' : rhoL L ⟨z, Subgroup.le_normalizer hzL⟩ = 1 := by
      simpa [show (⟨z, hHN hzH⟩ : ↥(normalizer (L : Set G))) =
          ⟨z, Subgroup.le_normalizer hzL⟩ from Subtype.ext rfl] using hrhz
    exact hznotO (hbar z hzL hrhz')
  have hrankq : 2 ≤ pRank p (⊤ : Subgroup (↥K ⧸ N')) :=
    CFSG.GroupTheory.two_le_pRank_of_commute (p := p) (H := ⊤) (x := qy) (y := qz)
      (Subgroup.mem_top qy) (Subgroup.mem_top qz) hqy hqz hcommq hindep
  calc
    2 ≤ pRank p (⊤ : Subgroup (↥K ⧸ N')) := hrankq
    _ = pRank p K := by
      rw [CFSG.SectionRank.pRank_quotient_eq (p := p) N' hcopN,
        ← pRank_eq_pRank_top_subgroup K]
    _ ≤ pRank p H := pRank_mono hp.one_lt hKH

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
