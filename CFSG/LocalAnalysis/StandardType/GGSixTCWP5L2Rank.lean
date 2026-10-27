module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4A5Close
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Aut
import CFSG.RankThree.PartTwo.Sec8.Hering418L2
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
import CFSG.LocalAnalysis.ComponentInitial.LiftOddQuotient
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Item413AutL2
import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
import CFSG.RankThree.PartTwo.Sec4.Item47
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import Certificates.Certificate2022
import Certificates.Certificate2022Base
import Certificates.Certificate2121
import Certificates.Certificate2122
import Certificates.Certificate2123
import Certificates.Certificate2202
import Certificates.Certificate2214
import Certificates.Certificate2215
import Certificates.Certificate2217
import Certificates.Certificate2283
import Certificates.Certificate2288
import Certificates.Certificate3084
import Certificates.Certificate3171
import Certificates.Certificate3171Base
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.GH74.GLS.Stage2.Bender.Thm1

private theorem w5A_ringChar_galoisField_two_ne_three (n : ℕ) :
    ringChar (GaloisField 2 n) ≠ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ringChar (GaloisField 2 n) = 2 := ringChar.eq _ 2
  omega

private theorem w5A_four_le_card_galoisField_two {n : ℕ} (hn : 2 ≤ n) :
    4 ≤ Nat.card (GaloisField 2 n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [GaloisField.card 2 n (by omega)]
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem elemAbelian3_card_le_nine_of_aut_psl2 {R : Type} [Group R] {n : ℕ} (hn : 2 ≤ n)
    (hR : LieModel R .PSL 2 2 n) (E : Subgroup (MulAut R)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  obtain ⟨e⟩ := CFSG.Quasithin.H13.nonempty_equiv_psl_of_lieModel (by omega) hR
  let B : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) :=
    E.map (MulAut.congr e).toMonoidHom
  have hBcard : Nat.card B = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hBe : IsElemAbelian 3 B := hE.map (MulAut.congr e).toMonoidHom
  have hB9 := CFSG.RankThree.PartTwo.Sec4.Hering418L2.card_le_nine_of_mulAut_PSL2
    (w5A_ringChar_galoisField_two_ne_three n) (w5A_four_le_card_galoisField_two hn) B hBe
  rw [← hBcard]
  exact hB9

theorem tcCard_le_of_L2 {X : Type} [Group X] [Finite X] {B D J : Subgroup X} {n : ℕ} (hn2 : 2 ≤ n)
    (hJ : Group.IsPerfect ↥J) (hB : IsElemAbelian 3 B)
    (hn : B ≤ Subgroup.normalizer (J : Set X)) (hc : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hD : Nat.card D = 3 ^ 2) (hmod : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 n) :
    Nat.card B ≤ 3 ^ 4 := by
  have : Group.IsPerfect ↥J := hJ
  set ψ : ↥B →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    (actCenterQuot J).comp (Subgroup.inclusion hn) with hψ
  have hψrange : IsElemAbelian 3 ψ.range := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact (hB.subgroupOf (Subgroup.normalizer (J : Set X))).map (actCenterQuot J)
  have hker : ψ.ker ≤ (B ⊓ Subgroup.centralizer (J : Set X)).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf]
    refine ⟨b.2, ?_⟩
    show (b : X) ∈ Subgroup.centralizer (J : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (commute_of_actCenterQuot_eq_one J ⟨b, hn b.2⟩ hb j hj).symm
  have hcardB : Nat.card ↥B = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      mul_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker]
  have hker_card : Nat.card ψ.ker ≤
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) := by
    have h1 := Subgroup.card_le_of_le hker
    have h2 : Nat.card ↥((B ⊓ Subgroup.centralizer (J : Set X)).subgroupOf B) =
        Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2] at h1
    exact h1
  have hker9 : Nat.card ψ.ker ≤ 9 := by
    have h1 : Nat.card ψ.ker ≤ Nat.card D := by
      rw [← hc]
      exact hker_card
    rw [hD] at h1
    norm_num at h1
    exact h1
  have hrange9 : Nat.card ψ.range ≤ 9 :=
    elemAbelian3_card_le_nine_of_aut_psl2 hn2 hmod ψ.range hψrange
  rw [hcardB]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ 9 * 9 := Nat.mul_le_mul hker9 hrange9
    _ = 3 ^ 4 := by norm_num

end CFSG.StandardType.TableCRes

end
