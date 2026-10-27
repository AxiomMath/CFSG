module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Transport
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.EichlerFixLine
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove

open CFSG.Open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem centMove_of_quadraticForm {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hnd : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K (ι → K))
    {e : ι → K} (he : Q e = 0) (he0 : e ≠ 0) : CentMove (StatedOmega Q₀) e := by
  intro u hu
  obtain ⟨g, hg, hgu, hge⟩ := exists_mem_commutator_fix_and_move_line hnd hdim he he0 hu
  refine ⟨(toLinEquiv ι K).symm g, ?_, ?_, ?_⟩
  · rw [statedOmega_eq_comap hQ, Subgroup.mem_comap]
    simpa using hg
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    exact hgu
  · intro c hc
    apply hge c
    rw [← toLinEquiv_apply] at hc
    simpa using hc

theorem centMove_statedOmega_plus {m : ℕ} (hm : 2 ≤ m) {e : Fin m ⊕ Fin m → K}
    (he : StatedQuadPlus m K e = 0) (he0 : e ≠ 0) :
    CentMove (StatedOmega (StatedQuadPlus m K)) e := by
  have hQ : ⇑(CFSG.LieType.Universal.Spin.quadPlus m K) = StatedQuadPlus m K :=
    CFSG.LieType.Universal.Spin.coe_quadPlus m K
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K
  have hdim : 4 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
    omega
  have he' : CFSG.LieType.Universal.Spin.quadPlus m K e = 0 := by
    rwa [hQ]
  exact centMove_of_quadraticForm hQ hnd hdim he' he0

theorem centMove_statedOmega_minus {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {e : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K}
    (he : StatedQuadMinus m K b c e = 0) (he0 : e ≠ 0) :
    CentMove (StatedOmega (StatedQuadMinus m K b c)) e := by
  have hQ : ⇑(CFSG.LieType.Universal.Spin.quadMinus m K b c) = StatedQuadMinus m K b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus m K b c
  have hnd :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hdim : 4 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
    omega
  have he' : CFSG.LieType.Universal.Spin.quadMinus m K b c e = 0 := by
    rwa [hQ]
  exact centMove_of_quadraticForm hQ hnd hdim he' he0

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove
