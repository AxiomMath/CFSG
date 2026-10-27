module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.OvergroupHull CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G]

theorem inter_pointClass_eq {D : Set G} {K Lu LA A : Subgroup G} (hKu : K ≤ Lu) (hKA : K ≤ LA)
    (hLA : LA ≤ Subgroup.centralizer (A : Set G))
    (hinv : ∀ g ∈ Lu ⊓ Subgroup.centralizer (A : Set G), g ^ 2 = 1 → g ∈ K)
    (hD : ∀ x ∈ D, x ^ 2 = 1) :
    D ∩ (Lu : Set G) ∩ (LA : Set G) = D ∩ (K : Set G) := by
  ext x
  constructor
  · rintro ⟨⟨hxD, hxu⟩, hxA⟩
    exact ⟨hxD, hinv x ⟨hxu, hLA hxA⟩ (hD x hxD)⟩
  · rintro ⟨hxD, hxK⟩
    exact ⟨⟨hxD, hKu hxK⟩, hKA hxK⟩

theorem card_baseOrbit_le [Finite G] {H V W : Subgroup G} (hVW : V ≤ W) :
    Nat.card (baseOrbit H V) ≤ Nat.card (baseOrbit H W) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (fun ω ⟨x, hx, hxω⟩ => ⟨x, hVW hx, hxω⟩) (Set.toFinite _)

variable [Finite G]

theorem card_baseOrbit_pair_hull_le
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    Nat.card (baseOrbit H (minimalLocalFailureProperPairHull H z beta t)) ≤
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 + 1 := by
  obtain ⟨-, -, -, hmodel, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  rcases hmodel with
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard⟩
  · change Nat.card {ω : rightCosetSpace H //
      ∃ x ∈ minimalLocalFailureProperPairHull H z beta t, rightCosetMk H x = ω} ≤ _
    rw [hcard]
    have : Nat.card (minimalLocalFailurePairActionPointHull H z) ≤
        Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    omega
  · exact hcard.le

theorem not_le_of_degree
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y Lu : Subgroup G}
    (hdeg : Nat.card (baseOrbit H (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)))) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1)
    (hint : involutionPointClass z ∩ (Lu : Set G) ∩
        (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) : Set G) =
      involutionPointClass z ∩ (minimalLocalFailureProperPairHull H z beta t : Set G)) :
    ¬ Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ≤ Lu := by
  intro hle
  set LA := Subgroup.closure (involutionPointClass z ∩ (Y : Set G))
  have hLAK : LA ≤ minimalLocalFailureProperPairHull H z beta t := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxLA : x ∈ LA := Subgroup.subset_closure hx
    have hmem : x ∈ involutionPointClass z ∩ (Lu : Set G) ∩ (LA : Set G) :=
      ⟨⟨hx.1, hle hxLA⟩, hxLA⟩
    rw [hint] at hmem
    exact hmem.2
  have hcard := (card_baseOrbit_le (H := H) hLAK).trans
    (card_baseOrbit_pair_hull_le h hcomm hsmallerR1 hbeta ht hproper)
  rw [hdeg] at hcard
  obtain ⟨-, -, -, -, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hlt : Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 <
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

omit [Finite G] in
theorem closure_pointClass_inter_closure (z : G) (Y : Subgroup G) :
    Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) =
      Subgroup.closure (involutionPointClass z ∩
        (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) : Set G)) := by
  have hLY : Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ≤ Y :=
    (Subgroup.closure_le _).mpr Set.inter_subset_right
  exact le_antisymm (Subgroup.closure_mono fun x hx => ⟨hx.1, Subgroup.subset_closure hx⟩)
    (Subgroup.closure_mono (Set.inter_subset_inter_right _ hLY))

theorem sup_eq_top_of_ne
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y Y' : Subgroup G}
    (hKY : minimalLocalFailureProperPairHull H z beta t ≤
      Subgroup.closure (involutionPointClass z ∩ (Y : Set G)))
    (hU : IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z))
      (Subgroup.closure (involutionPointClass z ∩ (Y : Set G))))
    (hU' : IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z))
      (Subgroup.closure (involutionPointClass z ∩ (Y' : Set G))))
    (hne : Subgroup.closure (involutionPointClass z ∩ (Y' : Set G)) ≠
      Subgroup.closure (involutionPointClass z ∩ (Y : Set G))) :
    Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ⊔
      Subgroup.closure (involutionPointClass z ∩ (Y' : Set G)) = ⊤ := by
  by_contra htop
  set W := Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ⊔
    Subgroup.closure (involutionPointClass z ∩ (Y' : Set G))
  exact hne (minimalLocalFailure_proper_overgroup_unitary_hull_unique h hcomm hsmallerR1 hbeta ht
    hproper (lt_top_iff_ne_top.mpr htop) (hKY.trans le_sup_left) le_sup_right le_sup_left
    (closure_pointClass_inter_closure z Y') (closure_pointClass_inter_closure z Y) hU' hU)

end CFSG.ShultStronglyClosedTI.UnitaryHulls
