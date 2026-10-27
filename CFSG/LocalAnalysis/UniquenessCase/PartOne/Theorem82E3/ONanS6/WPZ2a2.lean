module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK332
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1
public import CFSG.GroupTheory.CentralizerQuotientCard
public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.Background.G25Seven
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.Quasithin.EmptyFaithful.SBc15R3G
public import CFSG.Quasithin.EmptyFaithful.SBc16SComp
public import CFSG.Quasithin.EmptyFaithful.SBc16SWr
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5L
public import CFSG.Quasithin.H13.L32NThm1443
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofPara
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldExc
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem isWeaklyClosedIn_of_isSylowOf_of_isPGroup
    {p : ℕ} [Fact p.Prime] {P Z R : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤)
    (hwc : IsWeaklyClosedIn Z P) (hR : IsPGroup p R) (hZR : Z ≤ R) :
    IsWeaklyClosedIn Z R :=
  fun _ hg => UCK.N588A.conjugate_eq_of_le_isPGroup hP hwc hR hZR hg

theorem weaklyClosedIn_Z0_S'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    (S : Subgroup ↥(G0 c P J)) (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤)
    (hZ0S : Z0 c P J ≤ S) :
    IsWeaklyClosedIn (Z0 c P J) S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let G₀ : Subgroup G := G0 c P J
  let Z : Subgroup G := zSub P c.L
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ :=
    isSylowOf_top_of_normalizer_le hP
      (normalizer_sylow_le_M_of_onan c hON hP hNZ)
  have hwcP : IsWeaklyClosedIn Z P :=
    weaklyClosed_zSub_of_onan_cover' c hON h7 hP hNZ
  have hR : IsPGroup 3 (S.map G₀.subtype) := hS.isPGroup.map G₀.subtype
  have hmapZ : (Z0 c P J).map G₀.subtype = Z :=
    Subgroup.map_subgroupOf_eq_of_le (le_sup_right : Z ≤ G₀)
  have hZR : Z ≤ S.map G₀.subtype := by
    rw [← hmapZ]
    exact Subgroup.map_mono hZ0S
  have hwcR : IsWeaklyClosedIn Z (S.map G₀.subtype) :=
    isWeaklyClosedIn_of_isSylowOf_of_isPGroup hPtop hwcP hR hZR
  intro g hg
  have hg' : CFSG.conjugate Z (g : G) ≤ S.map G₀.subtype := by
    rw [← hmapZ]
    change CFSG.conjugate ((Z0 c P J).map G₀.subtype) (G₀.subtype g) ≤ _
    rw [← CFSG.map_conjugate]
    exact Subgroup.map_mono hg
  have hEq : CFSG.conjugate Z (g : G) = Z := hwcR (g : G) hg'
  apply Subgroup.map_injective G₀.subtype_injective
  rw [CFSG.map_conjugate, hmapZ]
  exact hEq

theorem exists_sylow_setup'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J) :
    ∃ S : Subgroup ↥(G0 c P J), CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧
      CFSG.Open.pRank 3 S ≤ 3 ∧ Z0 c P J ≤ S ∧ IsWeaklyClosedIn (Z0 c P J) S ∧
      CFSG.Open.pRank 3 (Xbar c P J) ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hZ0card : Nat.card (Z0 c P J) = 3 := by
    change Nat.card ((zSub P c.L).subgroupOf (G0 c P J)) = 3
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : zSub P c.L ≤ G0 c P J)).toEquiv).trans hZcard
  have hZ0p : IsPGroup 3 (Z0 c P J) :=
    IsPGroup.of_card (n := 1) (by rw [hZ0card]; norm_num)
  obtain ⟨S, hZ0S⟩ := hZ0p.exists_le_sylow
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (S : Subgroup ↥(G0 c P J)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by
      simpa [Subgroup.relIndex_top_right] using S.not_dvd_index⟩
  have hpS : CFSG.Open.pRank 3 (S : Subgroup ↥(G0 c P J)) ≤ 3 := by
    have h1 : CFSG.Open.pRank 3 (S : Subgroup ↥(G0 c P J)) ≤
        CFSG.Open.pRank 3 ((S : Subgroup ↥(G0 c P J)).map (G0 c P J).subtype) :=
      CFSG.SectionRank.pRank_le_map Nat.prime_three.one_lt (G0 c P J).subtype
        (G0 c P J).subtype_injective (S : Subgroup ↥(G0 c P J))
    have h2 : CFSG.Open.pRank 3 ((S : Subgroup ↥(G0 c P J)).map (G0 c P J).subtype) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
      CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top
    exact h1.trans (h2.trans (pRank_three_G_le_three c hON hP hNZ))
  refine ⟨(S : Subgroup ↥(G0 c P J)), hS, hpS, hZ0S, ?_,
    pRank_Xbar_le_three c hON hP hNZ⟩
  exact weaklyClosedIn_Z0_S' c hON h7 hP hNZ haL ha3 haZ hJ h3
    (S : Subgroup ↥(G0 c P J)) hS hZ0S

theorem threeTwo_route''
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : 3 ∣ Nat.card J)
    (hK : K332Z3)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (Xcl c P J)) :
    (CFSG.Open.IsKGroup ↥(G0 c P J) ∧ Nat.card (Z0 c P J) = 3 ∧
        ∃ S : Subgroup ↥(G0 c P J), CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧
          CFSG.Open.pRank 3 S ≤ 3 ∧ Z0 c P J ≤ S ∧ IsWeaklyClosedIn (Z0 c P J) S ∧
          CFSG.Open.pRank 3 (Xbar c P J) ≤ 3) ∧
      (IsoGTwoPrime (Xbar c P J) ∨
        Nonempty (Xbar c P J ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
  classical
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha3
    norm_num at ha3
  have hJ_le_C : J ≤ Subgroup.centralizer ({a} : Set G) := by
    obtain ⟨L, -, hLJ⟩ := hJ
    rw [← hLJ]
    exact Subgroup.map_subtype_le L
  have hZ_le_C : zSub P c.L ≤ Subgroup.centralizer ({a} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hz.2 a haL).symm
  have hG0_le_C : G0 c P J ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [G0]
    exact sup_le hJ_le_C hZ_le_C
  have hK0 : CFSG.Open.IsKGroup ↥(G0 c P J) :=
    CFSG.AGLEmbedding.AscEightFour.isKGroup_mono
      (isKGroup_centralizer c ha1) hG0_le_C
  have hZcard : Nat.card (zSub P c.L) = 3 :=
    c.card_inf_centralizer_of_onan hON hP
  have hZ0card : Nat.card (Z0 c P J) = 3 := by
    change Nat.card ((zSub P c.L).subgroupOf (G0 c P J)) = 3
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : zSub P c.L ≤ G0 c P J)).toEquiv).trans hZcard
  obtain ⟨S, hS, hpS, hZ0S, hwc, hpX⟩ :=
    exists_sylow_setup' c hON h7 hP hNZ haL ha3 haZ hJ h3
  refine ⟨⟨hK0, hZ0card, S, hS, hpS, hZ0S, hwc, hpX⟩, ?_⟩
  have hmain := hK (↥(G0 c P J)) hK0 S (Z0 c P J) hS hpS hZ0S hZ0card hwc h2
  exact hmain

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
