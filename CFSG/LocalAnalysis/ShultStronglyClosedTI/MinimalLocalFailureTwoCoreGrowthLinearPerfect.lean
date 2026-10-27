module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_proper_pair_quasisimple
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    CFSG.Open.IsQuasisimple K ∧ Subgroup.center K = CFSG.oddCore K ∧
      Odd (Nat.card (Subgroup.center K)) := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  let V := (minimalLocalFailurePairActionPointHull H z).subgroupOf K
  obtain ⟨hVM, hnormal, hV, hcard, hgen⟩ :=
    CyclicPair.proper_pair_internal_elementary_hull h hcomm hbeta ht hproper
  exact normal_elementary_hull_quasisimple M V
    (minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper)
    hVM hnormal hV hcard hgen

theorem original_proper_pair_perfect
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    Group.IsPerfect (minimalLocalFailureProperPairHull H z beta t) := by
  exact ⟨(original_proper_pair_quasisimple h hcomm hbeta ht hproper).1.1⟩

theorem original_proper_pair_ambient_derived
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    ⁅K, K⁆ = K := by
  exact Subgroup.isPerfect_iff.mp
    (original_proper_pair_perfect h hcomm hbeta ht hproper)

theorem original_proper_pair_abelianization_subsingleton
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    Subsingleton (Abelianization (minimalLocalFailureProperPairHull H z beta t)) := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let : Group.IsPerfect K := original_proper_pair_perfect h hcomm hbeta ht hproper
  change Subsingleton (K ⧸ commutator K)
  infer_instance

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
