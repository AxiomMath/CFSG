module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem generation_of_noncentral_triple_subgroup
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {X : Subgroup G} (hXE : X ≤ triplePointStabilizer H z beta)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G))
    {v : G} (hv : v ∈ rightPairFlipFiber H z beta) :
    (Subgroup.zpowers z ⊔ Subgroup.zpowers v) ⊔ pairOddCore H beta = ⊤ := by
  by_contra hnot
  have hproper : minimalLocalFailureProperPairHull H z beta v < ⊤ :=
    lt_of_le_of_lt (sylowAssemblyProper_pair_hull_le_generated h hbeta hv)
      (lt_of_le_of_ne le_top hnot)
  have hWJ := sylowAssemblyProper_class_commutators_le_pair_oddCore
    h hcomm hbeta hv hproper
  have hE := (minimalLocalFailurePairAction h hbeta hv hproper hWJ).2.2.2
  apply hnoncentral
  intro x hx
  have hxE := hXE hx
  rw [hE] at hxE
  exact hxE.2

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
