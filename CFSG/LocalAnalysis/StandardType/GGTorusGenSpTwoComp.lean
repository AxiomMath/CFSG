module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Centralizer
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsFrame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearThreeTwo
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Open (StatedSp)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

theorem exists_mem_of_isComponentOf_centralizer_spTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) {E : Subgroup (StatedSp m K)}
    (hE : IsElemAbelian 3 E)
    (hEsc : ∀ Z : StatedSp m K, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E)
    {x : StatedSp m K} (hx : x ∈ E) (hx1 : x ≠ 1) {J : Subgroup (StatedSp m K)}
    (hJ : IsComponentOf J (Subgroup.centralizer {x})) : ∃ w ∈ J, w ∈ E ∧ w ≠ 1 := by
  have hx3 : x ^ 3 = 1 := hE.2 x hx
  have hblocks := spBlocks_three_two hK hm hx3 hx1
  obtain ⟨hJnorm, -⟩ := SevSpNs.exists_spSupported_of_isComponentOf (f := 1) (p := 3)
    (by rw [hK]; norm_num) (by norm_num) Nat.prime_three (by norm_num) hx3 hblocks hJ
  have hE_le_C : E ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) := by
    intro e he
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨e, he⟩)
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp hJ.2.2
  have hJne : J ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot J).mp (CFSG.LocalCores.isQuasisimple_nontrivial hJq)
  have hNoNorm := noNormalPPrime_three_centralizer_statedSp hK hm hx3 hx1
  have h3dvd : 3 ∣ Nat.card J := by
    rw [Nat.prime_three.dvd_iff_not_coprime]
    intro hc
    exact hJne (hNoNorm J hJ.1 hJnorm hc)
  have hE3 : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g.1 g.2)⟩
  have hEnorm : ∀ a ∈ E, ∀ l ∈ J, a * l * a⁻¹ ∈ J :=
    fun a ha l hl => hJnorm a (hE_le_C ha) l hl
  obtain ⟨w, hwJ, hw1, hw3, hwcomm⟩ := SevSpNs.exists_mem_inf_centralizer
    (H := StatedSp m K) Nat.prime_three (A := E) (N := J) hE3 hEnorm h3dvd
  exact ⟨w, hwJ, hEsc w (fun Y hY => (hwcomm Y hY).symm) hw3, hw1⟩

theorem ggTorusCompMeetSC_spTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    GGTorusCompMeetSC 3 (LargeEvenProj (LargeEvenSpGroup K m)) := by
  have : NeZero m := ⟨by omega⟩
  refine ggTorusCompMeetSC_of_mulEquiv (TableBSymp.spProjEquivSp (K := K) (m := m)) ?_
  intro E hE _ hEsc x hx hx1 J hJ
  exact exists_mem_of_isComponentOf_centralizer_spTwo hK hm hE hEsc hx hx1 hJ

end CFSG.StandardType
