module

public import CFSG.Quasithin.Background.SmithB42Dispatch
public import CFSG.Quasithin.Background.SmithB42Vacuous
public import CFSG.Quasithin.Background.SmithB42L2Even
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42Alt6
public import CFSG.Quasithin.Background.SmithB42Alt7
public import CFSG.Quasithin.Background.SmithB42G2Main
public import CFSG.Quasithin.Background.SmithB42SL3Even
public import CFSG.Quasithin.Background.SmithB42Sp4Main
public import CFSG.Quasithin.Background.SmithB42HatA6
public import CFSG.Quasithin.Background.SmithB42U33
public import CFSG.Quasithin.Background.SmithB42Tits
public import CFSG.Quasithin.Background.SmithB42F4Main
public import CFSG.Quasithin.Background.SmithB42LnL52
public import CFSG.Quasithin.Background.SmithB42G2FMain
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.Quasithin.Background.SmithB42LnL42
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.B1More13
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.FFC5Final
public import CFSG.Quasithin.Background.FFC6K
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.SmithB51SL3M
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.Quasithin

theorem asB42_holds
    : AsB42 :=
  asB42_of_families asB42U3Even_holds asB42Sz_holds asB42TrialityD4_holds
      (asB42ReeF4_of_large asB42ReeF4Large_holds) asB42L2Even_holds asB42L32_holds asB42L3Even_holds
      asB42Sp4Even_holds (asB42G2Even_holds gm04G2EvenFFNatural_holds) asB42U33_holds asB42L42_holds
      asB42L52_holds asB42Alt5_holds asB42Alt6_holds asB42HatA6_holds asB42Alt7_holds

end CFSG.Quasithin
