module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaCoreContainmentSaturation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaCoreContainmentConstrained
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaZJ
import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ThetaCoreContainment

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem odd_subgroup_saturation_captures_complement
    (J X : Subgroup G) (hJodd : Odd (Nat.card J)) (hXJ : X ≤ J)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (hXp : IsPGroup p X)
    (hcentral : ∀ x : G, x ∈ J → x ∈ Subgroup.centralizer (X : Set G) →
      CFSG.IsPElement p x → x ∈ X)
    (W : Subgroup G) (hWJ : W ≤ J) (hWcop : Nat.Coprime p (Nat.card W))
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ (CFSG.pPrimeCore p J).map J.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard J hJodd
  let A := X.subgroupOf J
  let K := W.subgroupOf J
  have hA : IsPGroup p A := hXp.comap_subtype
  have hKcop : Nat.Coprime p (Nat.card K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWJ).toEquiv]
    exact hWcop
  have hcentralJ : ∀ x : J, x ∈ Subgroup.centralizer (A : Set J) →
      orderOf x = p → x ∈ A := by
    intro x hxcent hxorder
    have hxcentG : (x : G) ∈ Subgroup.centralizer (X : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      let aJ : J := ⟨a, hXJ ha⟩
      have haA : aJ ∈ A := ha
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hxcent) aJ haA)
    exact hcentral x x.property hxcentG
      ⟨1, by simpa only [pow_one] using (Subgroup.orderOf_coe x).trans hxorder⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set J) := by
    intro a ha
    apply Subgroup.mem_normalizer_iff.mpr
    intro b
    change ((b : G) ∈ W ↔ (a * b * a⁻¹ : J).val ∈ W)
    exact Subgroup.mem_normalizer_iff.mp (hXW ha) b.val
  have hchar := LocalTheta.solvable_complement_quotient_characteristic_p
    (G := J) hp
  have hcapture := thompson_bender_core_of_characteristic_quotient
    hp hpodd hchar A hA hcentralJ K hKcop hAK
  have hm := Subgroup.map_mono (f := J.subtype) hcapture
  rwa [Subgroup.map_subgroupOf_eq_of_le hWJ] at hm

theorem minimalLocalFailure_theta_core_containment
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    let B := pairPointStabilizer H beta
    let E := triplePointStabilizer H z beta
    let J := pairOddCore H beta
    let V := (CFSG.oddCore E).map E.subtype
    ∀ P : Sylow p V,
      let X := (P : Subgroup V).map V.subtype
      rightConjugate X z = X → ¬ X ≤ Subgroup.centralizer ({z} : Set G) →
      ∀ t : G, t ∈ rightPairFlipFiber H z beta →
        t ∈ Subgroup.normalizer (X : Set G) →
        2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
          (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)) →
        V = J ⊓ E ∧
          (∀ x : G, x ∈ J → x ∈ Subgroup.centralizer (X : Set G) →
            CFSG.IsPElement p x → x ∈ X) ∧
          (∀ W : Subgroup G, W ≤ J → Nat.Coprime p (Nat.card W) →
            X ≤ Subgroup.normalizer (W : Set G) →
              W ≤ (CFSG.pPrimeCore p J).map J.subtype) ∧
          minimalLocalFailurePairConfinementTheta p E ≤
            minimalLocalFailurePairConfinementTheta p B := by
  let : Fact p.Prime := ⟨hp⟩
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let J := pairOddCore H beta
  let V := (CFSG.oddCore E).map E.subtype
  change ∀ P : Sylow p V,
    let X := (P : Subgroup V).map V.subtype
    rightConjugate X z = X → ¬ X ≤ Subgroup.centralizer ({z} : Set G) →
    ∀ t : G, t ∈ rightPairFlipFiber H z beta →
      t ∈ Subgroup.normalizer (X : Set G) →
      2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
        (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)) →
      V = J ⊓ E ∧
        (∀ x : G, x ∈ J → x ∈ Subgroup.centralizer (X : Set G) →
          CFSG.IsPElement p x → x ∈ X) ∧
        (∀ W : Subgroup G, W ≤ J → Nat.Coprime p (Nat.card W) →
          X ≤ Subgroup.normalizer (W : Set G) →
            W ≤ (CFSG.pPrimeCore p J).map J.subtype) ∧
        minimalLocalFailurePairConfinementTheta p E ≤
          minimalLocalFailurePairConfinementTheta p B
  intro P
  let X := (P : Subgroup V).map V.subtype
  change rightConjugate X z = X → ¬ X ≤ Subgroup.centralizer ({z} : Set G) →
    ∀ t : G, t ∈ rightPairFlipFiber H z beta →
      t ∈ Subgroup.normalizer (X : Set G) →
      2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
        (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)) →
      V = J ⊓ E ∧
        (∀ x : G, x ∈ J → x ∈ Subgroup.centralizer (X : Set G) →
          CFSG.IsPElement p x → x ∈ X) ∧
        (∀ W : Subgroup G, W ≤ J → Nat.Coprime p (Nat.card W) →
          X ≤ Subgroup.normalizer (W : Set G) →
            W ≤ (CFSG.pPrimeCore p J).map J.subtype) ∧
        minimalLocalFailurePairConfinementTheta p E ≤
          minimalLocalFailurePairConfinementTheta p B
  intro hXz hnoncentral t ht htX hrank
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hV : V = J ⊓ E := triple_odd_core_eq_pair_intersection
    h.local_datum S hzS hzcenter beta hbeta
  have hVJ : V ≤ J := by rw [hV]; exact inf_le_left
  have hXV : X ≤ V := Subgroup.map_subtype_le _
  have hcentral := original_triple_odd_sylow_centralizer_saturated
    h hFR beta hbeta p hp hpodd P hXz hnoncentral t ht htX hrank
  have hcapture : ∀ W : Subgroup G, W ≤ J → Nat.Coprime p (Nat.card W) →
      X ≤ Subgroup.normalizer (W : Set G) → W ≤ (CFSG.pPrimeCore p J).map J.subtype := by
    intro W hWJ hWcop hXW
    exact odd_subgroup_saturation_captures_complement J X (pairOddCore_odd H beta)
      (hXV.trans hVJ) p hp hpodd (P.isPGroup'.map V.subtype) hcentral W hWJ hWcop hXW
  refine ⟨hV, hcentral, hcapture, ?_⟩
  have hthetaE : minimalLocalFailurePairConfinementTheta p E =
      (CFSG.pPrimeCore p V).map V.subtype :=
    generatedPairGrowth_ambient_canonical_core_eq E hp
  have hthetaB : minimalLocalFailurePairConfinementTheta p B =
      (CFSG.pPrimeCore p J).map J.subtype :=
    generatedPairGrowth_ambient_canonical_core_eq B hp
  rw [hthetaE, hthetaB]
  let W := (CFSG.pPrimeCore p V).map V.subtype
  have hWJ : W ≤ J := (Subgroup.map_subtype_le _).trans hVJ
  have hWcop : Nat.Coprime p (Nat.card W) := by
    rw [Subgroup.card_map_of_injective V.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := hXV.trans
    (Subgroup.le_normalizer.trans (generatedPairGrowth_normalizer_le_characteristic_image
      V (CFSG.pPrimeCore p V) inferInstance))
  exact hcapture W hWJ hWcop hXW

end CFSG.ShultStronglyClosedTI.ThetaCoreContainment
