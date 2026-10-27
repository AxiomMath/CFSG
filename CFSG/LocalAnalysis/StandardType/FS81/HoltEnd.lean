module

public import CFSG.LocalAnalysis.StandardType.FS81.HoltEndAux
public import CFSG.Holt.H78.Theorem1
public import CFSG.Holt.H78.Bridge
public import CFSG.Holt.General.DLineTools
public import CFSG.Holt.General.Simple
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.RankThree.PartTwo.Census.Alternating
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate8064
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import CFSG.Holt.CaseTwoBW
public import CFSG.Holt.General.Basic
public import CFSG.Holt.OddCoreTwoGroupBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.RankThree.Holt.Basic
public import CFSG.Walter.JRFacts
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem l3HoltEnd_holds
    : L3HoltEnd := by
  intro G _ _ hsimp hchar r Y S t hEm hYtop hSyl htS ht2 hcent hconj
  obtain ⟨P, hPS⟩ := fs81Hl_sylow2In_sylow hSyl htS hconj
  have htY : t ∈ Y := hSyl.1 htS
  have ht1 : (⟨t, htY⟩ : Y) ≠ 1 := by
    intro h
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  haveI : Nontrivial ↥Y := ⟨⟨⟨t, htY⟩, 1, ht1⟩⟩
  have hYnsolv : ¬ Group.IsSolvable ↥Y :=
    fs81Hl_not_solvable_of_commutator_top hEm.1
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    have hnonabY : ∃ a b : ↥Y, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hYnsolv (Group.isSolvable_of_comm fun a b => h a b)
    obtain ⟨a, b, hab⟩ := hnonabY
    exact ⟨(a : G), (b : G), fun hxy => hab (Subtype.ext hxy)⟩
  haveI : FaithfulSMul G (G ⧸ Y) :=
    CFSG.RankThree.PartTwo.Sec21.faithfulSMul_quotient_of_simple hYtop
  have hfix : ∀ q : G ⧸ Y, t • q = q ↔ q = ((1 : G) : G ⧸ Y) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [CFSG.RankThree.PartTwo.Sec21.smul_mk_eq_iff,
        CFSG.RankThree.PartTwo.Sec21.mk_eq_mk_one_iff]
      constructor
      · intro hg
        have hg' : g⁻¹ ∈ Y := hconj g⁻¹ (by simpa using hg)
        simpa using Y.inv_mem hg'
      · intro hg
        exact Y.mul_mem (Y.mul_mem (Y.inv_mem hg) htY) hg
  have hPc : (P : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcent p (hPS ▸ hp)
  have hT : CFSG.Holt.General.IsHoltTriple G (G ⧸ Y) t ((1 : G) : G ⧸ Y) :=
    { isPretransitive := inferInstance
      orderOf_eq_two := ht2
      smul_eq_iff := hfix
      exists_sylow := ⟨P, by rw [hPS]; exact htS, hPc⟩ }
  have hgood : CFSG.Holt.General.IsGoodZ G (G ⧸ Y) ((1 : G) : G ⧸ Y) ⊤ :=
    CFSG.Holt.H78.isGoodZ_top_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1 hT
  rcases (CFSG.Holt.General.isGoodZ_top_iff hnonab ((1 : G) : G ⧸ Y)).mp hgood with
    ⟨hBender, hSE⟩ | ⟨m, _, e, _⟩
  · have hSEY : CFSG.IsStronglyEmbedded Y := by
      rwa [MulAction.stabilizer_quotient] at hSE
    exact CFSG.Holt.General.false_of_fusionIsBenderGroup_of_le hBender hSEY P
      (by rw [hPS]; exact hSyl.1) le_rfl hYnsolv
  · have hgt : 2520 < Nat.card Y := fs81Hl_card_gt_2520 hEm
    have hcardG : Nat.card G = Nat.card (alternatingGroup (Fin (2 * m + 1))) :=
      Nat.card_congr e.toEquiv
    have hYle : Nat.card Y ≤ Nat.card G := Subgroup.card_le_card_group Y
    by_cases hm4 : 4 ≤ m
    · exact (CFSG.RankThree.PartTwo.Census.not_isCharTwoType_alternating
          (n := 2 * m + 1) (by omega))
        (CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv e hchar)
    · have hm3 : m = 2 ∨ m = 3 := by omega
      rcases hm3 with rfl | rfl
      · have hc : Nat.card (alternatingGroup (Fin (2 * 2 + 1))) = 60 := by
          rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
          decide
        have h2 : Nat.card Y ≤ 60 := hYle.trans (hcardG.trans hc).le
        omega
      · have hc : Nat.card (alternatingGroup (Fin (2 * 3 + 1))) = 2520 := by
          rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
          decide
        have h2 : Nat.card Y ≤ 2520 := hYle.trans (hcardG.trans hc).le
        omega

end CFSG.StandardType.FrameRoute.FS81
