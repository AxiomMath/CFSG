module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRecognition
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84TorusModels
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem proper_pair_recognition
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    Nat.card K < Nat.card G ∧ 2 ≤ twoRank K ∧ R1Full K ∧
      CFSG.Open.IsQuasisimple K ∧ Subgroup.center K = CFSG.oddCore K ∧
      Odd (Nat.card (Subgroup.center K)) ∧
      fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  let V := (minimalLocalFailurePairActionPointHull H z).subgroupOf K
  have hstrict : Nat.card K < Nat.card G := by
    simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt hproper
  have hrank : 2 ≤ twoRank K := sylowAssemblyProper_pair_hull_rank_two h hbeta ht
  have hM : fusionStronglyEmbedded M :=
    minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper
  have hR1 : R1Full K := hsmallerR1 K hstrict hrank ⟨M, hM⟩
  obtain ⟨hVM, hnormal, hV, hcard, hgen⟩ :=
    proper_pair_internal_elementary_hull h hcomm hbeta ht hproper
  obtain ⟨hquasi, hcenter, hodd, hmodel⟩ :=
    normal_elementary_hull_recognition M V hM hVM hnormal hV hcard hgen hR1
  exact ⟨hstrict, hrank, hR1, hquasi, hcenter, hodd, hmodel⟩

theorem proper_pair_native_model_and_borel
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    Subgroup.center K = CFSG.oddCore K ∧
      IsSimpleBenderGroup (K ⧸ CFSG.oddCore K) ∧
      CFSG.oddCore K ≤ H.subgroupOf K ∧
      IsBorelSubgroup ((H.subgroupOf K).map (QuotientGroup.mk' (CFSG.oddCore K))) := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let V := (minimalLocalFailurePairActionPointHull H z).subgroupOf K
  obtain ⟨_, hrank, _, _, hcenter, _, _⟩ :=
    proper_pair_recognition h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨_, _, hV, _, hgen⟩ :=
    proper_pair_internal_elementary_hull h hcomm hbeta ht hproper
  have hcore : involutionCore K = ⊤ := involutionCore_eq_top_of_elementary_hull V hV hgen
  obtain ⟨hmodel, hoddPoint, hBorel⟩ := whole_involution_core_native_model_and_borel
    (H.subgroupOf K) (minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper)
    (native_rank_two_of_two_le_twoRank hrank) hcore
  exact ⟨hcenter, hmodel, hoddPoint, hBorel⟩

theorem proper_pair_full_inversion_torus
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    ∃ a : ℕ, 2 ≤ a ∧ IsSimpleBenderGroupAtExponent a (K ⧸ CFSG.oddCore K) ∧
      ∃ T : Subgroup G,
        (T : Set G) = {x : G | x ∈ H ⊓ rightConjugate H t ∧
          rightConjugateElem x t = x⁻¹ ∧ x ∈ K} ∧
        IsCyclic T ∧ Nat.card T = 2 ^ a - 1 := by
  let K := minimalLocalFailureProperPairHull H z beta t
  have htorder : orderOf t = 2 :=
    order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  have htinv : IsInvolution t :=
    ⟨(orderOf_eq_prime_iff.mp htorder).2, (orderOf_eq_prime_iff.mp htorder).1⟩
  have htH : t ∉ H := pair_flip_not_mem_point hbeta ht
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  obtain ⟨hcenter, hmodel, hcore, hB⟩ :=
    proper_pair_native_model_and_borel h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨a, ha, hmodelAt⟩ := hmodel.exists_exponent
  have hRcenter : twoPrimeCore K = Subgroup.center K := by
    rw [← oddCore_eq_twoPrimeCore]
    exact hcenter.symm
  have hcoreH : (twoPrimeCore K).map K.subtype ≤ H := by
    rw [← oddCore_eq_twoPrimeCore]
    exact (Subgroup.map_le_iff_le_comap).mpr hcore
  have hpoint : (K ⊓ H).subgroupOf K = H.subgroupOf K := by
    ext x
    change ((x : G) ∈ K ∧ (x : G) ∈ H) ↔ (x : G) ∈ H
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  let e : (K ⧸ CFSG.oddCore K) ≃* (K ⧸ twoPrimeCore K) :=
    QuotientGroup.quotientMulEquivOfEq (oddCore_eq_twoPrimeCore (G := K))
  have hqcomp : e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore K)) =
      QuotientGroup.mk' (twoPrimeCore K) := by
    apply MonoidHom.ext
    intro x
    exact QuotientGroup.quotientMulEquivOfEq_mk (oddCore_eq_twoPrimeCore (G := K)) x
  have hBmap :
      ((H.subgroupOf K).map (QuotientGroup.mk' (CFSG.oddCore K))).map
        e.toMonoidHom =
      ((K ⊓ H).subgroupOf K).map (QuotientGroup.mk' (twoPrimeCore K)) := by
    rw [Subgroup.map_map, hqcomp, hpoint]
  have hBorel : IsBorelSubgroup
      (((K ⊓ H).subgroupOf K).map (QuotientGroup.mk' (twoPrimeCore K))) := by
    rw [← hBmap]
    exact hB.map_mulEquiv e
  have hAt : IsSimpleBenderGroupAtExponent a (K ⧸ twoPrimeCore K) := by
    rcases hmodelAt with ⟨hlinear⟩ | ⟨⟨m, hm, hsuzuki⟩⟩ |
        ⟨⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, hunitary⟩⟩
    · exact IsSimpleBenderGroupAtExponent.isPSL2 ⟨e.symm.trans hlinear.some⟩
    · exact IsSimpleBenderGroupAtExponent.isSuzuki ⟨m, hm, ⟨e.symm.trans hsuzuki.some⟩⟩
    · exact IsSimpleBenderGroupAtExponent.isPSU3
        ⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, ⟨e.symm.trans hunitary.some⟩⟩
  obtain ⟨T, hTset, hTcyclic, hTcard⟩ :=
    proposition84_base_cyclicNormalizer_of_borel_model H K K t htinv htH htK
      le_rfl hRcenter hcoreH hBorel a ha hAt (fun _ hx => hx.2)
  refine ⟨a, ha, hmodelAt, T, ?_, hTcyclic, hTcard⟩
  simpa only [peterfalviKSet, Set.mem_ofPred_eq, and_assoc] using hTset

end CFSG.ShultStronglyClosedTI.CyclicPair
