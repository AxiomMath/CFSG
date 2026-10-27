module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelOdd
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_linear_point_kernel_and_odd_centralizers_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    LinearPointKernelConclusion H z beta t := by
  unfold LinearPointKernelConclusion
  intro B X K Q q J C M
  obtain ⟨hQ, ⟨e, hQe⟩, hQ4, -, hXB, hXnormal, hXcyclic, hXcard, hXreg, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hQH, -, hQnormal, -, -, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, hQM, -, -, hCM⟩ :=
    TwoCoreGrowth.original_point_root_centralizer_two_core h hcomm hbeta ht hproper
  have hQCM : Q ≤ Subgroup.centralizer (M : Set G) :=
    TwoCoreGrowth.original_point_hull_centralizes_two_core h.local_datum h.central_sylow
  have htwo := CyclicSemiregular.proper_pair_two_transitive h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, hn, -⟩ := minimalLocalFailure_linear_hull_proper_overgroups_normalize_of_conclusions
    h hcomm hsmallerR1 hbeta ht hproper hlin hexcl
  have hindex : B.relIndex H = q ^ 3 := by
    rw [pair_stabilizer_relIndex_eq hbeta htwo, hn, Nat.add_sub_cancel]
  obtain ⟨hNeq, hQB, -⟩ := point_normalizer_eq_root_sup h hcomm hsmallerR1 hbeta ht hproper hlin
  have hJ : J = B ⊓ Subgroup.centralizer (Q : Set G) :=
    pair_hull_centralizer_eq h hcomm hsmallerR1 hbeta ht hproper hlin
  obtain ⟨hNC, hQJ, hJQ, hidx⟩ :=
    root_centralizer_normalizer_and_index h hcomm hsmallerR1 hbeta ht hproper hlin hindex
  obtain ⟨u, huB, hu⟩ := proper_pair_stabilizer_exists_involution h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, hemb⟩ :=
    proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl
      huB hu
  have hinv : ∀ v ∈ B, orderOf v = 2 → v ∈ J := by
    intro v hvB hv
    obtain ⟨-, hKv, -⟩ :=
      PairInvolutionsCentralize.minimalLocalFailure_pair_involutions_centralize_point_group h
        hcomm hsmallerR1 hbeta ht hproper v hvB hv
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKv hk)
  have he : 1 ≤ e := by
    by_contra he
    have he0 : e = 0 := by omega
    rw [hQe, he0, pow_zero] at hQ4
    omega
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) :=
    (pairPointStabilizer_le_point H beta).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal)
  obtain ⟨k₀, _, _, hk₀, φ, ι, hker, hφι, himage⟩ :=
    regular_cyclic_semilinear_embedding hQ hQe he hBQ hXB hXnormal hXcyclic hXcard hXreg
  have hker' : ι.ker = J.subgroupOf B := by
    rw [hker, hJ]
    ext b
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  refine ⟨hlin, htwo, hindex, hNeq, hQB, hJ, hNC, hQJ, hJQ, hidx, hemb, hinv, hQM, hQCM, hCM,
    ⟨k₀, inferInstance, inferInstance, hk₀, φ, ι, hker', hφι, himage⟩, ?_⟩
  intro y hyJ hy1 hyodd
  exact odd_pair_centralizer_structure h hcomm hsmallerR1 hbeta ht hproper hlin hexcl hyJ hy1
    hyodd

end CFSG.ShultStronglyClosedTI.LinearChain
