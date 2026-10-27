module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedContradiction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplementBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexPointIndex

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.OvergroupHull
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem false_of_hulls
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hfix : Nat.card (rightFixedSet H u) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1)
    {P : Subgroup G} (hPB : P ≤ pairPointStabilizer H beta) (hP2 : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.relIndex (pairPointStabilizer H beta)) (huP : u ∈ P)
    (hPu : P ≤ Subgroup.centralizer {u})
    (hhull : UnitaryFixedHullsConclusion H z beta t u) : False := by
  obtain ⟨-, hLu, -, -, -, p, -, -, -, A, A₀, hA, -, -, -, hAK, hAu, -, -, -, -, -, hY, -, -,
    hLAusq, -, -, -, -, -, hoverlap, hLAnotle, -, -⟩ := hhull
  obtain ⟨huQ, huK, i, hi, hfixi, hdeg⟩ :=
    pairInvolutionCentralizesConclusion h hcomm hsmallerR1 hbeta ht hproper u huB hu
  obtain ⟨-, -, -, hQ, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hi3 : i = 3 := by
    have h1 := hfixi.symm.trans hfix
    exact Nat.pow_right_injective
      (by omega : 2 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z))
      (Nat.add_right_cancel h1)
  subst hi3
  obtain ⟨-, hYu, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      huB hu
  obtain ⟨-, hΔ, -, -, -, hzu, -⟩ :=
    MixedClass.minimalLocalFailure_mixed_involution_class_closure h hcomm hsmallerR1 hbeta ht
      hproper huB hu
  obtain ⟨hQclass, -, -⟩ := CyclicPair.proper_pair_point_root_classes h hcomm hbeta ht hproper
  have hKA : minimalLocalFailureProperPairHull H z beta t ≤ Subgroup.centralizer (A : Set G) :=
    fun k hk => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hAK ha) k hk).symm
  obtain ⟨-, ⟨Fu⟩⟩ := exists_unitaryHullCoordinates_of_isUnitaryScalarQuotient h hcomm hsmallerR1
    hbeta ht hproper hYu huK hLu
  obtain ⟨-, ⟨FA⟩⟩ := exists_unitaryHullCoordinates_of_isUnitaryScalarQuotient h hcomm hsmallerR1
    hbeta ht hproper hY hKA hLAusq
  obtain ⟨-, -, -, -, -, -, -, -, j, -, -, -, -, -, -, huniq⟩ :=
    minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta ht hproper hY
      hKA
  obtain ⟨hDK, -⟩ := minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1
    hbeta ht hproper hproper le_rfl
  have htwo := MixedClass.ambient_two_transitive h.local_datum h.central_sylow hQ hQ4 hQclass
  have hidx := LocalCriterionCosetNormalizerIndex.original_pair_index_of_double_transitivity
    H beta hbeta (fun a b c e hab hce => by
      obtain ⟨g, h1, h2⟩ := htwo a b c e hab hce
      exact ⟨g, (LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate H a g).trans h1,
        (LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate H b g).trans h2⟩)
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two
    (order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1)
  have hcoset : u • (minimalLocalFailurePairActionPointHull H z : Set G) ⊆
      involutionPointClass u := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact hΔ ⟨q, ⟨hq, huQ hq⟩, rfl⟩
  exact ExclusionSetup.false
    { Fu := Fu, FA := FA, datum := h.local_datum, point_class := hQclass
      flip_coset := flip_coset_eq H ht, beta_ne := hbeta, flip_sq := ht2
      pair_normalizes := TwoCoreGrowth.original_pair_hull_normalized h hcomm hbeta ht hproper
      pairHull_class := hDK, u_mem := huB, u_order := hu, u_point := huQ, u_pairHull := huK
      u_not_conj := hzu, coset_class := hcoset, degree := hdeg, pair_index := hidx
      P_le := hPB, P_two := hP2, P_index := hPidx, u_mem_P := huP, P_commute := hPu
      A_le_pair := fun _ ha => (hA ha).1, A_le_Lu := fun _ ha => (hA ha).2
      A_centralizes := hAK, A_u := hAu, overlap := hoverlap, LA_not_le := hLAnotle
      LA_unique := fun V hVY hV hVq => (huniq V hVY hV hVq).1, Lu_quotient := hLu }

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
