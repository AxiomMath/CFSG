module

public import CFSG.Open.StatedDefs
public import CFSG.LieType.SteinbergBROddSylowNormalizers
public import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Open

lemma statedClassicalModel_alt8_PSL42 :
    CFSG.Open.StatedClassicalModel (alternatingGroup (Fin 8)) .PSL 4 2 1 := by
  refine ⟨⟨Nat.prime_two, le_refl 1, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨?_⟩⟩
  exact CFSG.LieType.SteinbergBR.OddSylow.alternatingEightEquiv.trans
    (CFSG.RankThree.PartOne.CTP.projectiveSLEquivStated 4 (ZMod 2))

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
