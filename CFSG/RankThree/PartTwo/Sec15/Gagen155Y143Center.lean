module

import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Center
import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Use
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeSetup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y143

theorem center_map_eq_inf_of_ne_bot (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {B : Subgroup G} (hBA : IsHyperplane A B)
    {Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))} (hYc : CFSG.IsComponent Yc)
    (hne : (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ⊓ Yc ≠ ⊥) :
    SectionFourHyp ↥Yc ∧ Nat.card (Subgroup.center ↥Yc) = 3 ∧
      (Subgroup.center ↥Yc).map Yc.subtype =
        (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ⊓ Yc := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  have hT : TheoremFourHyp G := hR.toTheoremFourHyp
  have hA27 : Nat.card A = 27 := hR.mem_partTwoE.2.1
  have hB9 : Nat.card B = 9 := by
    have h := hBA.2
    rw [hA27] at h
    omega
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hZ : Subgroup.center G = ⊥ := by
      rcases hT.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hT.nonabelian
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hBZ : B ≤ Subgroup.center G := by
      intro b hb
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
    rw [hZ, le_bot_iff] at hBZ
    rw [hBZ, Subgroup.card_bot] at hB9
    norm_num at hB9
  have hC4 : SectionFourHyp ↥C := hT.sectionFourHyp hCtop
  have hY4 : SectionFourHyp ↥Yc :=
    Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore h1 hC4 hYc
  have hBZ' : B.subgroupOf C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp y.2 (x : G) hx).symm)
  have hBle : (B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ≤
      Subgroup.center (↥C ⧸ CFSG.pPrimeCore 3 ↥C) :=
    (Subgroup.map_mono hBZ').trans (Subgroup.map_center_le_center
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C)))
  have hinfZ : ((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓
      Yc).subgroupOf Yc ≤ Subgroup.center ↥Yc := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx' : (x : ↥C ⧸ CFSG.pPrimeCore 3 ↥C) ∈
        (B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓ Yc :=
      Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_center_iff.mp (hBle (Subgroup.mem_inf.mp hx').1) (y : _)
  have hinfSub_ne : ((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓
      Yc).subgroupOf Yc ≠ ⊥ := by
    intro hbot
    apply hne
    have hle : ((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓ Yc) ≤ Yc :=
      inf_le_right
    have h := congrArg (Subgroup.map Yc.subtype) hbot
    rw [Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hle] at h
    exact h
  have hZne : Subgroup.center ↥Yc ≠ ⊥ := by
    intro hZbot
    exact hinfSub_ne (le_bot_iff.mp (hZbot ▸ hinfZ))
  have hO : CFSG.pPrimeCore 3 (↥C ⧸ CFSG.pPrimeCore 3 ↥C) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hZp : IsPGroup 3 (Subgroup.center ↥Yc) :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree.isPGroup_center_of_isComponent
      hYc hO
  have hnd9 : ¬ 9 ∣ Nat.card (Subgroup.center ↥Yc) := fun h9 =>
    Sylow155T51.false_of_nine_dvd_card_center h2 h43 hin hY4 hYc.1 hZp h9
  have hZcard : Nat.card (Subgroup.center ↥Yc) = 3 := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZne (Subgroup.eq_bot_of_card_eq (Subgroup.center ↥Yc) (by rw [hk, pow_zero]))
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      apply hnd9
      rw [hk]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [pow_add]
      exact ⟨3 ^ j, by ring⟩
    have hk1 : k = 1 := by omega
    rw [hk, hk1, pow_one]
  have hsubcard : Nat.card (((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓
      Yc).subgroupOf Yc) = 3 := by
    have hdvd := Subgroup.card_dvd_of_le hinfZ
    rw [hZcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hinfSub_ne
    · exact h3
  have heq : ((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓
      Yc).subgroupOf Yc = Subgroup.center ↥Yc :=
    Subgroup.eq_of_le_of_card_ge hinfZ (by rw [hZcard, hsubcard])
  refine ⟨hY4, hZcard, ?_⟩
  have hmap := congrArg (Subgroup.map Yc.subtype) heq
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right :
    ((B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓ Yc) ≤ Yc)] at hmap
  exact hmap.symm

end Gagen155Y143

end CFSG.RankThree.PartTwo.Sec15
