module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowLocal
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylowTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerAction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
open CFSG.ShultStronglyClosedTI.CentralizerSylow

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailure_centralizer_sylow_involution_normalizer
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (X : Subgroup G) (hXH : X ≤ H) (hXz : rightConjugate X z = X)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G))
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (Q : Sylow p (pairPointStabilizer H beta.val ⊓
      Subgroup.centralizer (X : Set G) : Subgroup G)) :
    ∃ s ∈ conjugacyWithin H z,
      s ∈ Subgroup.normalizer (X : Set G) ∧
      s ∈ Subgroup.normalizer
        (((Q : Subgroup (pairPointStabilizer H beta.val ⊓
          Subgroup.centralizer (X : Set G) : Subgroup G)).map
            (pairPointStabilizer H beta.val ⊓ Subgroup.centralizer (X : Set G)).subtype :
              Subgroup G) : Set G) ∧
      s ∈ Subgroup.normalizer
        ((X ⊔ (Q : Subgroup (pairPointStabilizer H beta.val ⊓
          Subgroup.centralizer (X : Set G) : Subgroup G)).map
            (pairPointStabilizer H beta.val ⊓ Subgroup.centralizer (X : Set G)).subtype :
              Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let C := pairPointStabilizer H beta.val ⊓ Subgroup.centralizer (X : Set G)
  let QG := (Q : Subgroup C).map C.subtype
  have hQY : QG ≤ Y := ((Subgroup.map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer (X : Set G))
  let U := QG.subgroupOf Y
  let F0 := L ⊔ U
  let F := F0.map Y.subtype
  let Delta := numeratorRightOrbit H Y (rightCosetMk H 1)
  have hXne : X ≠ ⊥ := by
    intro hh
    exact hnoncentral (hh ▸ bot_le)
  have hQp : IsPGroup p QG := Q.isPGroup'.map C.subtype
  have hUodd : Odd (Nat.card U) := by
    obtain ⟨n, hn⟩ := hQp.comap_subtype.exists_card_eq (G := U)
    rw [hn]
    exact hpodd.pow
  obtain ⟨hF0card, hF0rank, hF0strong, _hF0trans, _hF0double, _hcoreA, _hcorefix⟩ :=
    leastFailure_local_normalizer_odd_join_action
      h X hXH hXne hXz hescape hrank U hUodd beta hbeta
  obtain ⟨_hproperY, _hcardY, _hlocalY, _hcentralY, _hnormalL, _hstrongL,
    _hclassL, hLright, _hfixedX⟩ :=
    leastFailure_local_normalizer_hull h X hXH hXne hXz hescape
  have hFY : F ≤ Y := Subgroup.map_subtype_le _
  have hQF : QG ≤ F := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQY]
    exact Subgroup.map_mono (le_sup_right : U ≤ F0)
  have hzF : z ∈ F := Subgroup.mem_map_of_mem Y.subtype
    ((le_sup_left : L ≤ F0) (localPointHull_distinguished_mem zY))
  have hFstrong : fusionStronglyEmbedded (H.subgroupOf F) :=
    local_normalizer_internal_point_embedding H Y F0 hF0strong
  let e : F0 ≃* F := F0.equivMapOfInjective Y.subtype Y.subtype_injective
  have hFrank : TwoRankAtLeastTwo F := hF0rank.map_of_injective e.toMonoidHom e.injective
  have hFcard : Nat.card F < Nat.card G := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hF0card
  have hR1 : R1Full F := hFR F hFcard (two_le_twoRank_of_native hFrank)
    ⟨H.subgroupOf F, hFstrong⟩
  have hFstable : ∀ f ∈ F, ∀ omega ∈ Delta,
      pointRightCosetMul H omega f ∈ Delta := by
    intro f hf omega homega
    exact numeratorRightOrbit_stable H Y _ f (hFY hf) omega homega
  have hLimage (l : L) : (l.val : G) ∈ F :=
    Subgroup.mem_map_of_mem Y.subtype ((le_sup_left : L ≤ F0) l.property)
  have htransRight : ∀ omega ∈ Delta, ∃ f : F,
      pointRightCosetMul H (rightCosetMk H 1) f.val = omega := by
    intro omega homega
    obtain ⟨l, hl⟩ := hLright
      ⟨rightCosetMk H 1, numeratorRightOrbit_base H Y _⟩ ⟨omega, homega⟩
    exact ⟨⟨l.val.val, hLimage l⟩, hl⟩
  have hFtrans : letI := pointInvariantSetInverseRightAction H F Delta hFstable
      MulAction.IsPretransitive F Delta := by
    let := pointInvariantSetInverseRightAction H F Delta hFstable
    constructor
    intro a b
    obtain ⟨l, hl⟩ := hLright a b
    refine ⟨⟨l.val.val⁻¹, F.inv_mem (hLimage l)⟩, Subtype.ext ?_⟩
    change pointRightCosetMul H a.val (l.val.val⁻¹)⁻¹ = b.val
    simpa only [inv_inv] using hl
  have hRA : CFSG.oddCore F ≤ H.subgroupOf F :=
    oddCore_le_of_rank_two_stronglyEmbedded (H.subgroupOf F)
      (native_strong_embedding_of_order_conditions hFstrong) hFrank
  have hRH : (CFSG.oddCore F).map F.subtype ≤ H := by
    rintro r ⟨rF, hrF, rfl⟩
    exact hRA hrF
  have hcoreFix := noncentralSylow_normal_subgroup_fixes_transitive_orbit
    F.subtype H (CFSG.oddCore F) hRH Delta htransRight
  have hRfix : ∀ omega ∈ Delta, ∀ r ∈ (CFSG.oddCore F).map F.subtype,
      pointRightCosetMul H omega r = omega := by
    rintro omega homega r ⟨rF, hrF, rfl⟩
    exact hcoreFix omega homega rF hrF
  exact local_centralizer_sylow_involution_normalizer
    H X F hFY Delta hFstable (numeratorRightOrbit_base H Y _)
    beta.val hbeta beta.property hFrank hR1 hFstrong hFtrans z
    h.local_datum.distinguished_mem hzF h.local_datum.distinguished_order
    hnoncentral hRfix p hp hpodd Q hQF

end CFSG.ShultStronglyClosedTI
