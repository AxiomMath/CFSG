module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementContradiction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowth
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailurePairConfinement
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : ∀ a b : pointRightCosetSpace H, a ≠ b →
      ∀ v : G, v ∈ involutionPointClass z → pointRightCosetMul H a v = a →
        ∀ t : G, t ∈ involutionPointClass z →
          pointRightCosetMul H a t = b → pointRightCosetMul H b t = a →
            (Subgroup.zpowers v ⊔ Subgroup.zpowers t) ⊔
              (CFSG.oddCore (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
                (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).subtype = ⊤)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hpdiv : p ∣ Nat.card (conjugacyWithin H z))
    (P : Subgroup G) (hPH : P ≤ H) (hP : IsPGroup p P)
    (hPz : CFSG.conjugate P z = P)
    (hmotion : p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤
      Nat.card (conjugacyWithin P z)) :
    Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H := by
  have hz := h.local_datum.distinguished_order
  have hzP := primeComplementGrowth_mem_normalizer_of_conjugate_eq P z hPz
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hPcard⟩ := hP.exists_card_eq
  have hPodd : Odd (Nat.card P) := hPcard ▸ hpodd.pow
  have hzclass : z ∈ conjugacyWithin H z := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one]
  let : Nonempty (conjugacyWithin H z) := ⟨⟨z, hzclass⟩⟩
  have hpart : 1 < p ^ (Nat.card (conjugacyWithin H z)).factorization p :=
    Nat.one_lt_pow (Nat.ne_of_gt (hp.factorization_pos_of_dvd Nat.card_pos.ne' hpdiv))
      hp.one_lt
  have hIcard := pairConfinement_inverted_card_eq_class P hPodd z hz hzP
  have hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1 :=
    pairConfinement_inverted_nonidentity_of_card P z (by omega)
  by_contra hescape
  let M := Subgroup.centralizer (minimalLocalFailureInvertedSet P z)
  let A := minimalLocalFailureInvertedOvergroup P z
  let L := minimalLocalFailureInvertedHull P z
  obtain ⟨X, hXHL, hXodd, hXnormal, _, hNescape, _, hcomm, _⟩ :=
    invertedHull_full_stabilizer_supplement h P hPodd hI hescape
  obtain ⟨hkernelNormal, _, hkernelIndex, _, _, _, _⟩ :=
    invertedHull_odd_core_structure h P hPodd hI hescape
  have hXM : X ≤ M := pairConfinement_odd_supplement_centralizes L M X
    (hXHL.trans inf_le_right) hkernelNormal hkernelIndex hXodd
  let N := Subgroup.normalizer (X : Set G) ⊓ L
  have hzL : z ∈ L := invertedHull_distinguished_mem P z
  have hzN : z ∈ N := ⟨
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXHL).mp hXnormal
      ⟨h.local_datum.distinguished_mem, hzL⟩, hzL⟩
  have hLA : L ≤ A := by
    let zA : A := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
    exact Subgroup.map_subtype_le (involutionPointHull zA)
  have hNA : N ≤ A := inf_le_right.trans hLA
  obtain ⟨s, hsN, hsH, hmax⟩ :=
    pairConfinement_theta_maximizing_conjugate h.local_datum N hNescape p
  obtain ⟨n, hn⟩ := hsN
  change rightConjugateElem z (n : G) = s at hn
  have hsclass : s ∈ involutionPointClass z := ⟨(n : G), hn⟩
  have hnH : (n : G) ∉ H := by
    intro hnmem
    apply hsH
    rw [← hn]
    exact (pointClass_conjugate_mem_iff h.local_datum (n : G)).mpr hnmem
  have hnA : (n : G) ∈ A := hNA n.property
  have hsA : s ∈ A := by
    rw [← hn]
    exact A.mul_mem (A.mul_mem (A.inv_mem hnA)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))) hnA
  have hsNmem : s ∈ N := by
    rw [← hn]
    exact N.mul_mem (N.mul_mem (N.inv_mem n.property) hzN) n.property
  let V := minimalLocalFailurePairConfinementClosure P z
  let J := rightConjugate H (n : G)
  let D := H ⊓ rightConjugate H s
  let gamma := rightCosetMk H (n : G)
  obtain ⟨hVB, hVD, hsV⟩ :=
    pairConfinement_closure_pair_intersections H P z hz hPH (n : G) hnA
  rw [hn] at hVD hsV
  have hV : IsPGroup p V := hP.of_injective
    (Subgroup.inclusion (pairConfinement_closure_le P z))
    (Subgroup.inclusion_injective (pairConfinement_closure_le P z))
  have hsorder := order_two_of_mem_pointClass hz hsclass
  have hsinvert : ∀ x ∈ minimalLocalFailureInvertedSet P z,
      rightConjugateElem x s = x⁻¹ := by
    rw [← hn]
    exact invertedHull_conjugates_invert_set P z hz (n : G) hnA
  have hVmotion : p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤
      Nat.card (conjugacyWithin V s) := by
    rw [pairConfinement_closure_class_card P hPodd z s hz hsorder hzP hsV hsinvert]
    exact hmotion
  have hgamma : pointRightCosetMul H gamma s = gamma := by
    rw [← hn]
    exact point_class_conjugate_fixed_rightCoset h.local_datum (n : G)
  have hgammaNe : gamma ≠ rightCosetMk H 1 := by
    intro heq
    have hrel := Quotient.exact heq
    change (QuotientGroup.rightRel H) (n : G) 1 at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    exact hnH (H.inv_mem_iff.mp (by simpa only [one_mul] using hrel))
  let beta := rightCosetMk J (n : G)⁻¹
  have hbeta : beta ≠ rightCosetMk J 1 := by
    intro heq
    have hh := congrArg (rebaseRightCoset H (n : G)) heq
    change rebaseRightCoset H (n : G) (rightCosetMk J (n : G)⁻¹) =
      rebaseRightCoset H (n : G) (rightCosetMk J 1) at hh
    rw [rebaseRightCoset_mk, rebaseRightCoset_mk, mul_inv_cancel, mul_one] at hh
    exact hgammaNe hh.symm
  have hlocal : InvolutionPointLocalEmbedding J s := by
    rw [← hn]
    exact local_point_datum_right_conjugate h.local_datum (n : G)
  have hscentral : InvolutionPointCentralSylow s := by
    rw [← hn]
    exact minimalLocalFailure_central_sylow_right_conjugate h.central_sylow (n : G)
  obtain ⟨S, hsS, hscenter⟩ := hscentral
  have hVpair : V ≤ pairPointStabilizer J beta := by
    rw [pairConfinement_rebased_pair]
    exact hVB
  obtain ⟨Q, _, hQtriple, _⟩ := triple_motion_threshold_contains_pair_sylow hlocal
    S hsS hscenter beta hbeta p hp V hVpair hV hsV (by
      rw [← hn]
      rw [right_conjugate_point_class_card H z (n : G)]
      rw [hn]
      exact hVmotion)
  obtain ⟨t, ht⟩ := original_pair_flip_exists hlocal beta hbeta
  have htclass : t ∈ involutionPointClass z := (pointClass_eq_of_mem hsclass) ▸ ht.1
  have hbaseImage : rebaseRightCoset H (n : G) (rightCosetMk J 1) = gamma := by
    rw [rebaseRightCoset_mk, mul_one]
  have hbetaImage : rebaseRightCoset H (n : G) beta = rightCosetMk H 1 := by
    rw [rebaseRightCoset_mk, mul_inv_cancel]
  have htforward : pointRightCosetMul H gamma t = rightCosetMk H 1 := by
    have hh := congrArg (rebaseRightCoset H (n : G)) ht.2
    rwa [rebaseRightCoset_translate, hbaseImage, hbetaImage,
      ← pointRightCosetMul_eq_translate] at hh
  have htback : pointRightCosetMul H (rightCosetMk H 1) t = gamma := by
    have hh := congrArg (rebaseRightCoset H (n : G)) (right_pair_flip_returns hsorder ht)
    rwa [rebaseRightCoset_translate, hbaseImage, hbetaImage,
      ← pointRightCosetMul_eq_translate] at hh
  have hgenOriginal := hgen gamma (rightCosetMk H 1) hgammaNe s hsclass hgamma
    t htclass htforward htback
  have hgenPair : (Subgroup.zpowers s ⊔ Subgroup.zpowers t) ⊔ pairOddCore J beta = ⊤ := by
    unfold pairOddCore
    rw [pairConfinement_rebased_pair]
    change (Subgroup.zpowers s ⊔ Subgroup.zpowers t) ⊔
      (CFSG.oddCore (rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H
        (rightCosetMk H 1) : Subgroup G)).map _ = ⊤ at hgenOriginal
    rw [rightCosetStabilizer_base, rightCosetStabilizer_mk, inf_comm] at hgenOriginal
    exact hgenOriginal
  obtain ⟨hsimple, hnonabelian⟩ := minimalLocalFailure_nonabelian_simple h
  let : IsSimpleGroup G := hsimple
  have hgrowth := (local_involution_point_generated_pair_strict_core_growth hnonabelian
    hlocal S hsS hscenter hbeta ht hgenPair p hp hpodd ⟨Q, hQtriple⟩).1
  change minimalLocalFailurePairConfinementTheta p (triplePointStabilizer J s beta) <
    minimalLocalFailurePairConfinementTheta p (pairPointStabilizer J beta) at hgrowth
  rw [pairConfinement_rebased_pair, pairConfinement_rebased_triple] at hgrowth
  obtain ⟨r, hrN, hrH, hrpair⟩ := pairConfinement_restricted_flip_intersection
    h.local_datum N hzN hNescape (n : G) n.property hnH
  have hmaxB := hmax r hrN hrH
  rw [hrpair] at hmaxB
  have hthetaEscape : ¬ minimalLocalFailurePairConfinementTheta p D ≤ J :=
    pairConfinement_theta_escape_of_growth p hp H J D inf_le_left hgrowth hmaxB
  have hVgamma : V ≤ rightCosetStabilizer H gamma := by
    rw [rightCosetStabilizer_mk]
    exact hVB.trans inf_le_right
  exact pairConfinement_theta_escape_contradiction h P X (hXHL.trans inf_le_left) hXM
    hcomm p hp hpodd s hsclass hsA hsNmem.1 gamma hgamma hV hVgamma hVD hsinvert
    (by rwa [rightCosetStabilizer_mk])

end CFSG.ShultStronglyClosedTI
