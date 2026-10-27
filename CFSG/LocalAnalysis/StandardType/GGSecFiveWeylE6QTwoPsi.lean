module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
public import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Chevalley

theorem ggSecFiveData_of_twistedE6Model
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hG : ChevalleyExceptionalModel G .twistedE6 2 1) (hG0 : ggG0 p B x L D J = ⊤) :
    GGSecFiveData p B x L D J := by
  obtain ⟨Kf, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hG
  obtain ⟨e'⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four (by rw [hcard]; norm_num)
    σ.toRingHom (fun c => by simpa using hσ c)
  let ψ : (ggU .twistedE6 0 1).K →* G :=
    ((e.trans e').symm).toMonoidHom.comp CFSG.EvenSmallLie.TwoE6.isogenyStd
  have hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 0 1).K := by
    have hψ : ψ.ker = CFSG.EvenSmallLie.TwoE6.isogenyStd.ker := by
      ext z
      exact (e.trans e').symm.map_eq_one_iff
    rw [hψ]
    exact CFSG.EvenSmallLie.TwoE6.ker_isogenyStd_le_center
  have hrange : ψ.range = ggG0 p B x L D J := by
    rw [MonoidHom.range_eq_top.mpr
      ((e.trans e').symm.surjective.comp CFSG.EvenSmallLie.TwoE6.isogenyStd_surjective), hG0]
  exact Or.inr (Or.inr ⟨.twistedE6, 0, 1,
    ggSecFivePres_of_psi_twistedE6 hG.1 (by decide) ψ hker hrange⟩)

end CFSG.StandardType

end
