module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.StronglyEmbedded
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.RankThree.PartOne.LIT.RankPSL3
import CFSG.RankThree.PartOne.LIT.RankSuzuki
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.Open.PGLModelStated
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.Models.BenderSuzuki
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.BenderSuzuki
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem isStronglyEmbeddedOrder_of_isStronglyEmbedded {X : Type} [Group X] {M : Subgroup X}
    (h : CFSG.IsStronglyEmbedded M) : IsStronglyEmbeddedOrder M := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have := h.2.2 g⁻¹ fun hg' => hg (by simpa using M.inv_mem hg')
  rwa [CFSG.conjugate, inv_inv] at this

theorem le_pRank_three_of_isElemAb {X : Type} [Group X] [Finite X] {E : Subgroup X} {k : ℕ}
    (hE : IsElemAb 3 k E) : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.SectionRank.le_pRank (by norm_num) le_top
    ⟨hE.1.toIsMulCommutative, fun x hx => by
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.1.exponent_dvd_p ⟨x, hx⟩
      simpa using congrArg Subtype.val h⟩ hE.2

theorem kf_se3 : KF_SE3 := by
  intro X _ _ _ _ ⟨M, hM⟩ E k hE
  refine (le_pRank_three_of_isElemAb hE).trans ?_
  have h3 : (1 : ℕ) < 3 := by norm_num
  rcases bender_suzuki M (isStronglyEmbeddedOrder_of_isStronglyEmbedded hM) with
    ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · let e' : projSL 2 (GaloisField 2 n) ≃* PSL2Model n :=
      (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 2 (GaloisField 2 n)).trans
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 (GaloisField 2 n)))
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3 (e.trans e'.symm)]
    exact CFSG.RankThree.PartOne.LIT.pRank_projSL_two_le Nat.prime_three (by norm_num)
      (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup n)))]
    exact CFSG.RankThree.PartOne.LIT.pRank_suzukiMatrixGroup_le n Nat.prime_three (by norm_num)
  · let e' : projSU 3 2 n ≃* PSU3Model n :=
      ((CFSG.PGLModel.projSUEquivStatedProj 3 2 n).trans
          (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative n)).trans
        (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n).symm)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3 (e.trans e'.symm)]
    exact CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le (by omega) Nat.prime_three
      (by norm_num)

end CFSG.RankThree.PartTwo.Sec21.FF81
