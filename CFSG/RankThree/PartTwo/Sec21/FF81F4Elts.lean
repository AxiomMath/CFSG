
module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Roots
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl2
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Local
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
open CFSG.StandardType CFSG.StandardType.TableBF4TwoInputs CFSG.LieType.Chevalley.RootOps
open CFSG.Assembly

section Elts

noncomputable abbrev tE : F42C := f4Rep (ZMod 2) [47]

noncomputable abbrev uE : F42C := f4Rep (ZMod 2) [44]

noncomputable abbrev tuE : F42C := f4Rep (ZMod 2) [47, 44]

noncomputable abbrev vE : F42C := f4Rep (ZMod 2) [41, 45]

theorem hasBits_tE : HasBits (ZMod 2) tE tB :=
  hasBits_f4Rep_single 47 ⟨by norm_num, by norm_num⟩

theorem hasBits_uE : HasBits (ZMod 2) uE uB :=
  hasBits_f4Rep_single 44 ⟨by norm_num, by norm_num⟩

theorem hasBits_tuE : HasBits (ZMod 2) tuE tuB := by
  have h : tuE = tE * uE := f4Rep_pair 47 44
  rw [h]
  exact hasBits_tE.mul hasBits_uE

theorem hasBits_vE : HasBits (ZMod 2) vE vB := by
  have h : vE = f4Rep (ZMod 2) [41] * f4Rep (ZMod 2) [45] := f4Rep_pair 41 45
  rw [h]
  exact (hasBits_f4Rep_single (K := ZMod 2) 41 ⟨by norm_num, by norm_num⟩).mul
    (hasBits_f4Rep_single (K := ZMod 2) 45 ⟨by norm_num, by norm_num⟩)

noncomputable abbrev sE (i : Fin 4) : F42C := TableBF4Two.rho (ZMod 2) i (uSL 1 * vSL 1)

theorem hasBits_sE (i : Fin 4) : HasBits (ZMod 2) (sE i) (sB i) := by
  fin_cases i
  · exact hasBits_rho 0
  · exact hasBits_rho 1
  · exact hasBits_rho 2
  · exact hasBits_rho 3

noncomputable abbrev rAE : F42C := sE 3

noncomputable abbrev rBE : F42C := sE 0 * sE 1

noncomputable abbrev zE : F42C := (sE 0 * sE 0) * (sE 1 * sE 1) * (sE 2 * sE 2)

theorem hasBits_rAE : HasBits (ZMod 2) rAE rAB := hasBits_sE 3

theorem hasBits_rBE : HasBits (ZMod 2) rBE rBB := (hasBits_sE 0).mul (hasBits_sE 1)

theorem hasBits_zE : HasBits (ZMod 2) zE zB :=
  (((hasBits_sE 0).mul (hasBits_sE 0)).mul ((hasBits_sE 1).mul (hasBits_sE 1))).mul
    ((hasBits_sE 2).mul (hasBits_sE 2))

end Elts

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
