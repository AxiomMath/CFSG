module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoE8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTwoD
public import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLong
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoMemberModels

public section

namespace CFSG.StandardType

namespace FieldTwoE8

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.RCKRP
open CFSG.Open (StatedLieTag)

section Cert

theorem exists_longSelectedSL2Model_E7 :
    ∃ δ, GGLongRoot (ggU .E7 0 1).D δ ∧
      Nonempty (SelectedRoot.SelectedSL2Model (ggU .E7 0 1).D (GaloisField 2 1) δ) := by
  obtain ⟨δ, ⟨m⟩⟩ := FieldTwoExc.exists_selectedSL2Model_E7
  refine ⟨δ, ?_, ⟨m⟩⟩
  have hsym : ∀ i j, (ggU .E7 0 1).D.cartan i j = (ggU .E7 0 1).D.cartan j i :=
    cartanE_symm 7
  exact ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7 hsym rfl
    m.root_mem

theorem exists_longSelectedSL2Model_twistedE6 :
    ∃ δ, GGLongRoot (ggU .twistedE6 0 1).D δ ∧
      Nonempty (SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 1).D (GaloisField 2 1) δ) :=
  ⟨_, (CFSG.StandardType.LieKnownR2.Short.f4_ggLongRoot_single_iff (GaloisField 2 1)
    ⟨1, by change 1 < Tag.rank .F4; decide⟩).2 le_rfl, exists_selectedSL2Model_twistedE6⟩

end Cert

end FieldTwoE8

end CFSG.StandardType

end
