module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.Open.StatedDefs
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet
import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.TableC

open CFSG.Open (StatedSp)

section NoFieldExt

theorem not_fieldExtCase_of_mulEquiv_statedSp
    {X : Type} [Group X] {J : Subgroup X} {m f : ℕ}
    {F : Type} [Field F] (hF : Nat.card F = 2 ^ f) (hm : 2 ≤ m) (hmf : (m, f) ≠ (2, 1))
    (e : ↥J ≃* ↥(StatedSp m F)) : ¬ GGSixLSevenFieldExtCase J .PSp f := by
  rintro ⟨t', m', f', hff, hL', -⟩
  have := CFSG.SeitzReduction.LinearPilot.charP_two_of_card_eq_two_pow hF
  have hZ : Subgroup.center ↥J = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => e.injective ?_
    have hz' : e z ∈ Subgroup.center ↥(StatedSp m F) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      simpa using congrArg e (hz (e.symm g))
    rw [CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by omega), Subgroup.mem_bot] at hz'
    simpa using hz'
  have e' : (↥J ⧸ Subgroup.center ↥J) ≃* ↥(StatedSp m F) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hL := CFSG.SeitzReduction.SymplecticPilot.lieModel_of_mulEquiv_statedSp e' hF hm hmf
  have hdet := CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet m _ f t' m' f' hL
    (CFSG.Blueprint.LieModel.admissible hL') hL'
  omega

end NoFieldExt

end CFSG.StandardType.TableC

end
