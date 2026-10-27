module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTypes
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwo
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.RankThree.Asc83Table.E27
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47LThree
import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows
import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

theorem isSimpleGroup_of_type148
    {X : Type} [Group X] (hXp : Group.IsPerfect X)
    (ht : Type148 X) : IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := by
    rcases ht with h | ⟨p, f, hp, -, hf, hL⟩ | hA7 | hM12 | hM22 | hJ2
    · exact (Main148.isSimpleGroup_of_type429 hXp (Or.inl h)).1
    · rcases hL with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
        exact MulEquiv.isSimpleGroup φ
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf hq.ne'
        exact MulEquiv.isSimpleGroup φ
    · exact (Main148.isSimpleGroup_of_type429 hXp (Or.inr (Or.inl hA7))).1
    · exact (Main148.isSimpleGroup_of_type429 hXp (Or.inr (Or.inr (Or.inl hM12)))).1
    · exact (Main148.isSimpleGroup_of_type429 hXp (Or.inr (Or.inr (Or.inr (Or.inl hM22))))).1
    · exact (Main148.isSimpleGroup_of_type429 hXp (Or.inr (Or.inr (Or.inr (Or.inr hJ2))))).1
  have : Nontrivial X := hs.toNontrivial
  exact ⟨hs, Main148.exists_ne_comm_of_isPerfect hXp⟩

theorem three_dvd_card_of_type148 {X : Type} [Group X] (ht : Type148 X) : 3 ∣ Nat.card X := by
  rcases ht with h | ⟨p, f, hp, -, hf, hL⟩ | hA7 | hM12 | hM22 | hJ2
  · exact Main148.three_dvd_card_of_type429 (Or.inl h)
  · exact Main148.three_dvd_card_of_isLThreeEpsAt148 hf hL
  · exact Main148.three_dvd_card_of_type429 (Or.inr (Or.inl hA7))
  · exact Main148.three_dvd_card_of_type429 (Or.inr (Or.inr (Or.inl hM12)))
  · exact Main148.three_dvd_card_of_type429 (Or.inr (Or.inr (Or.inr (Or.inl hM22))))
  · exact Main148.three_dvd_card_of_type429 (Or.inr (Or.inr (Or.inr (Or.inr hJ2))))

theorem center_eq_bot_of_type148
    {X : Type} [Group X] (hXp : Group.IsPerfect X)
    (ht : Type148 X) : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup X := (isSimpleGroup_of_type148 hXp ht).1
  exact Sec4.RonanK429.center_eq_bot_of_isSimpleGroup_of_isPerfect

theorem false_of_e9_le_mulAut_l32 {X : Type} [Group X]
    (φ : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1))
    (E : Subgroup (MulAut X)) (hE : Nat.card E = 9) (hE3 : ∀ x ∈ E, x ^ 3 = 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1)) :=
    Finite.of_equiv _ (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 1)).symm.toEquiv
  haveI : Finite X := Finite.of_equiv _ φ.toEquiv.symm
  haveI : Finite (MulAut X) := MulEquiv.finite_left
  haveI hcomm : IsMulCommutative E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE]; norm_num)
  have hEea : CFSG.IsElementaryAbelian 3 E :=
    { is_comm := hcomm.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hE3 _ g.2) }
  have h2 : 2 ≤ CFSG.pRank 3 (MulAut X) :=
    CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (by norm_num) hEea (k := 2)
      (by rw [hE]; norm_num)
  rw [CFSG.RankThree.Asc83Table.pRank_congr (MulAut.congr φ)] at h2
  have h1 := CFSG.RankThree.PartTwo.Sec4.pRank_three_mulAut_projSL_three_two_le_one
  exact absurd (le_trans h2 h1) (by norm_num)

theorem type148_wrongSign_or_type429 {X : Type} [Group X] (ht : Type148 X) :
    Main148.Type429 X ∨ ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
      ((p ^ f % 3 = 2 ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f))) ∨
        (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧
          Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f))) := by
  by_cases hE : ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
      ((p ^ f % 3 = 2 ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f))) ∨
        (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧
          Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f)))
  · exact Or.inr hE
  · exact Or.inl (Main148.type429_of_type148 ht hE)

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
