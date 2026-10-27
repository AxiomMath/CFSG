module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.Open.StatedDefs
public import CFSG.CharacterTheory.Semidihedral.RecognitionRemaining
public import CFSG.CharacterTheory.Semidihedral.AllPrimeQDInputs
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeStationaryCoverageProof
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate110
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3120
public import Certificates.Certificate8046
public import Certificates.Certificate8052
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.lr_wreathed_simple_recognition_1
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hwr : ∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* WreathedTwoGroup n)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        StatedClassicalModel G .PSU 3 p f) :=
  CFSG.Semidihedral.RecognitionFromGaps.wreathed_recognition_of_theoremBStar
    CFSG.Semidihedral.AllPrime.stationaryCoverageStatement
    CFSG.Wreathed.OriginalAllPrime.stationaryCoverageStatement_holds G hnonab hwr

end CFSG.Open

namespace CFSG.Open

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.lr_wreathed_simple_recognition_2
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hwr : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* WreathedTwoGroup n)) :
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* PSL(3, GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* PSU3 p k)) :=
  CFSG.Semidihedral.RecognitionFromGaps.wreathed_catalogue_of_theoremBStar
    CFSG.Semidihedral.AllPrime.stationaryCoverageStatement
    CFSG.Wreathed.OriginalAllPrime.stationaryCoverageStatement_holds G hnonab P hwr

end CFSG.Open
