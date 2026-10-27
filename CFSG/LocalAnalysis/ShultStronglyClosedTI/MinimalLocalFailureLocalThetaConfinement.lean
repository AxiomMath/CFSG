module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

theorem centralizer_factorization_commutator_mem
    (O J : Subgroup G) (hOJ : O ≤ Subgroup.normalizer (J : Set G)) {z : G}
    (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hfactor : (O : Set G) =
      (O ⊓ Subgroup.centralizer ({z} : Set G) : Set G) * (J : Set G))
    {g : G} (hg : g ∈ O) : ⁅g, z⁆ ∈ J := by
  have hgp : g ∈ (O ⊓ Subgroup.centralizer ({z} : Set G) : Set G) * (J : Set G) :=
    hfactor ▸ hg
  obtain ⟨c, hc, j, hj, rfl⟩ := Set.mem_mul.mp hgp
  have hcent : Commute c z := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hcommJ : ⁅j, z⁆ ∈ J := by
    have hjconj := (Subgroup.mem_normalizer_iff.mp hzJ j⁻¹).mp (J.inv_mem hj)
    simpa only [commutatorElement_def, mul_assoc] using J.mul_mem hj hjconj
  have hconj := (Subgroup.mem_normalizer_iff.mp (hOJ hc.1) ⁅j, z⁆).mp hcommJ
  have heq : ⁅c * j, z⁆ = c * ⁅j, z⁆ * c⁻¹ := by
    calc
      ⁅c * j, z⁆ = c * j * z * j⁻¹ * (c⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
      _ = c * j * z * j⁻¹ * (z⁻¹ * c⁻¹) := by rw [hcent.inv_left.inv_right.eq]
      _ = c * ⁅j, z⁆ * c⁻¹ := by simp only [commutatorElement_def, mul_assoc]
  exact heq.symm ▸ hconj

theorem triple_distinguished_commutator_mem_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {g : G} (hg : g ∈ triplePointStabilizer H z beta) :
    ⁅g, z⁆ ∈ (CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype := by
  let E := triplePointStabilizer H z beta
  let O := oppositePairStabilizer H z beta
  let J := oppositePairOddCore H z beta
  have hOJ : O ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.le_normalizer.trans (generatedPairGrowth_normalizer_le_characteristic_image
      O (CFSG.oddCore O) (CFSG.ComponentClassification.OddCore.characteristic O))
  have hzJ : z ∈ Subgroup.normalizer (J : Set G) :=
    (opposite_pair_odd_core_odd_and_normalized h beta).2
  have hcommJ : ⁅g, z⁆ ∈ J := centralizer_factorization_commutator_mem O J hOJ hzJ
    (opposite_pair_eq_z_centralizer_mul_odd_core h S hzS hzcenter beta hbeta)
    (triple_stabilizer_le_opposite_pair H z beta hg)
  have hcommE : ⁅g, z⁆ ∈ E := by
    have hh := (Subgroup.mem_normalizer_iff.mp
      (triple_stabilizer_normalized_by_distinguished h beta) g⁻¹).mp (E.inv_mem hg)
    simpa only [commutatorElement_def, mul_assoc] using E.mul_mem hg hh
  rw [triple_odd_core_eq_opposite_pair_intersection h S hzS hzcenter beta hbeta]
  exact ⟨hcommJ, hcommE⟩

theorem local_theta_odd_core_le_triple [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) :
    let Y := Subgroup.normalizer (X : Set G)
    let D := Y ⊓ pairPointStabilizer H beta.val
    let T := Y ⊓ pairOddCore H beta.val
    let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    (CFSG.oddCore K).map K.subtype ≤ Y ⊓ triplePointStabilizer H z beta.val := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let D := Y ⊓ pairPointStabilizer H beta.val
  let T := Y ⊓ pairOddCore H beta.val
  let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  let UY := U.subgroupOf Y
  let F := L ⊔ UY
  let f := Y.subtype.comp F.subtype
  let R := (CFSG.oddCore K).map K.subtype
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨_hDpoint, _hTD, _hTnormal, hUD, _hUnormal, hUodd, _hpart, _hSylow,
    _hIpoint, _hInormal, hzI, hKpoint, _hKnorm, _hIKnormal, _hgen, _hUprod, _hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S hzS hzcenter Y hzY hescape beta hbeta hp
  have hUY : U ≤ Y := hUD.trans inf_le_left
  have hUYodd : Odd (Nat.card UY) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv]
    exact hUodd
  obtain ⟨_hcard, _hrank, _hstrong, _htrans, _hdouble, _hcoreA, hcorefix⟩ :=
    leastFailure_local_normalizer_odd_join_action h X hXH hXne hXz hescape hrank
      UY hUYodd beta hbeta
  obtain ⟨_hsol, _hKrank, _htwo, _hclass, kF, _hkinj, hkcomp, _hkernel,
    _helem, hcoreimage⟩ := local_theta_actual_structure h hcomm X hXH hXne hXz
      hescape hrank beta hbeta hp
  let q := QuotientGroup.mk' (CFSG.oddCore F)
  let qK := q.comp kF
  let UK := U.subgroupOf K
  let M := (rightCosetStabilizer H beta.val).comap K.subtype
  have hUKM : UK ≤ M := by
    intro k hk
    exact (hUD hk).2.2
  have hkerM : qK.ker ≤ M := by
    intro k hk
    have hkcore : kF k ∈ CFSG.oddCore F :=
      (QuotientGroup.eq_one_iff (kF k)).mp (MonoidHom.mem_ker.mp hk)
    have hfix := congrArg Subtype.val (hcorefix beta ⟨kF k, hkcore⟩)
    change pointRightCosetMul H beta.val (f (kF k))⁻¹ = beta.val at hfix
    have hval : f (kF k) = (k : G) := DFunLike.congr_fun hkcomp k
    rw [hval] at hfix
    change (k : G) ∈ rightCosetStabilizer H beta.val
    apply (rightCosetStabilizer H beta.val).inv_mem_iff.mp
    exact (mem_point_right_stabilizer_iff H beta.val (k : G)⁻¹).mpr hfix
  have hcoreM : CFSG.oddCore K ≤ M :=
    (Subgroup.map_le_map_iff.mp hcoreimage).trans (sup_le hUKM hkerM)
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRB : R ≤ pairPointStabilizer H beta.val := by
    rintro r ⟨k, hk, rfl⟩
    refine ⟨?_, hcoreM hk⟩
    rw [rightCosetStabilizer_base]
    exact (hKpoint k.property).1
  have hRnorm : K ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (generatedPairGrowth_normalizer_le_characteristic_image
      K (CFSG.oddCore K) (CFSG.ComponentClassification.OddCore.characteristic K))
  have hzR : z ∈ Subgroup.normalizer (R : Set G) :=
    hRnorm ((le_sup_left : I ≤ K) hzI)
  exact le_inf (hRK.trans (hKpoint.trans inf_le_right))
    (invariant_pair_subgroup_le_triple hRB hzR)

end CFSG.ShultStronglyClosedTI.LocalTheta
