module

public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup CFSG.Open
open scoped commutatorElement
open CFSG.BenderSuzuki.MatrixGroups (HermitianForm ProjectiveSpecialUnitaryMatrixGroup)
open CFSG.UnitaryThreeRecognition.Model (rootGroup torusGroup)

theorem commutator_normalizer_rootGroup_le {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)
    (hq : 2 < p ^ f) :
    ⁅normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))⁆ ≤
        rootGroup J hJ := by
  set N := normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) with hNdef
  have hN : N = rootGroup J hJ ⊔ torusGroup J hJ := by
    rw [hNdef, CFSG.AGLEmbedding.UnitaryModel.normalizer_rootGroup_eq_stabilizer_pinf J hJ hK
      hfix hq, CFSG.UnitaryThreeRecognition.Model.rootGroup_sup_torusGroup J hJ (p ^ f) hK hfix]
  have hUN : rootGroup J hJ ≤ N := Subgroup.le_normalizer
  have hTN : torusGroup J hJ ≤ N := hN ▸ le_sup_right
  have hsup : (rootGroup J hJ).subgroupOf N ⊔ (torusGroup J hJ).subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUN hTN, ← hN, Subgroup.subgroupOf_self]
  have hTc : ∀ x ∈ torusGroup J hJ, ∀ y ∈ torusGroup J hJ, x * y = y * x := by
    intro x hx y hy
    have := CFSG.UnitaryThreeRecognition.Model.isCyclic_torusGroup J hJ (p ^ f) hK hfix
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := torusGroup J hJ)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : IsMulCommutative ((torusGroup J hJ).subgroupOf N) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hTc _ a.2 _ b.2))⟩⟩
  have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : ⁅(⟨a, ha⟩ : N), (⟨b, hb⟩ : N)⁆ ∈ _root_.commutator N :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h1 := hle hab
  rw [Subgroup.mem_subgroupOf] at h1
  simpa [commutatorElement_def] using h1

theorem exists_isCoatom_normalizer_of_psu {L : Type} [Group L] [Finite L] {f : ℕ}
    (h : StatedClassicalModel L .PSU 3 7 f) {R : Subgroup L} (hR : IsPGroup 7 R) :
    ∃ S : Subgroup L, R ≤ S ∧ IsPGroup 7 S ∧ IsCoatom (normalizer (S : Set L)) ∧
      ⁅normalizer (S : Set L), normalizer (S : Set L)⁆ ≤ S := by
  obtain ⟨hp, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu h
  have : Fact (Nat.Prime 7) := ⟨hp⟩
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  obtain ⟨P, hP⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_equiv_map_eq e T P
  refine ⟨T, hRT, T.isPGroup', ?_, ?_⟩
  · have hco := CFSG.AGLEmbedding.UnitaryModel.isCoatom_normalizer_rootGroup J hJ hK hfix hq
    rw [← hP, ← he', ← Subgroup.map_equiv_normalizer_eq] at hco
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e') _).mp hco
  · have hc := commutator_normalizer_rootGroup_le J hJ hK hfix hq
    rw [← hP, ← he', ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_commutator] at hc
    exact (Subgroup.map_le_map_iff_of_injective e'.injective).mp hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
