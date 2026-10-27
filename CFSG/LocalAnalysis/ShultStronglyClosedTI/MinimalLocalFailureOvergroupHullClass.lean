module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHull
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OvergroupHull

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_self_le (L : Subgroup G) : ⁅L, L⁆ ≤ L :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)

theorem mem_commutator_of_conj_mul {L : Subgroup G} {z w : G} (hzL : z ∈ L)
    (hw : w ∈ conjugacyWithin L z) (hzw : z * w ∈ conjugacyWithin L z) : z ∈ ⁅L, L⁆ := by
  have hconj : ∀ x ∈ conjugacyWithin L z, ∃ c ∈ ⁅L, L⁆, x = z * c := by
    rintro x ⟨a, rfl⟩
    refine ⟨⁅z⁻¹, (a : G)⁻¹⁆,
      Subgroup.commutator_mem_commutator (L.inv_mem hzL) (L.inv_mem a.2), ?_⟩
    simp only [commutatorElement_def, inv_inv, mul_assoc, mul_inv_cancel_left]
  obtain ⟨c₂, hc₂, hw'⟩ := hconj w hw
  obtain ⟨c₃, hc₃, hzw'⟩ := hconj _ hzw
  have hwc : w = c₃ := mul_left_cancel hzw'
  have hz : z = c₃ * c₂⁻¹ := by
    rw [← hwc, hw', mul_inv_cancel_right]
  rw [hz]
  exact ⁅L, L⁆.mul_mem hc₃ (⁅L, L⁆.inv_mem hc₂)

theorem isPerfect_of_class_closure {L : Subgroup G} {z w : G} (hzL : z ∈ L)
    (hgen : L = Subgroup.closure (conjugacyWithin L z))
    (hw : w ∈ conjugacyWithin L z) (hzw : z * w ∈ conjugacyWithin L z) :
    Group.IsPerfect L := by
  have hz := mem_commutator_of_conj_mul hzL hw hzw
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm (commutator_self_le L)
  conv_lhs => rw [hgen]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨a, rfl⟩
  have hc : ⁅z⁻¹, (a : G)⁻¹⁆ ∈ ⁅L, L⁆ :=
    Subgroup.commutator_mem_commutator (L.inv_mem hzL) (L.inv_mem a.2)
  have hx : (a : G)⁻¹ * z * a = z * ⁅z⁻¹, (a : G)⁻¹⁆ := by
    simp only [commutatorElement_def, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [SetLike.mem_coe, hx]
  exact ⁅L, L⁆.mul_mem hz hc

variable [Finite G]

theorem exists_mem_ne_ne {Q : Subgroup G} (hQ : 3 ≤ Nat.card Q) (a b : G) :
    ∃ w ∈ Q, w ≠ a ∧ w ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (Q : Set G) ⊆ {a, b} := fun w hw => by
    by_cases hwa : w = a
    · exact Or.inl hwa
    · exact Or.inr (hcon w hw hwa)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hpair : ({a, b} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hQn : Nat.card Q = (Q : Set G).ncard := Nat.card_coe_set_eq (Q : Set G)
  omega

theorem overgroup_class_eq {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y) :
    involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y z := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨hQclass, hclasses, -⟩ :=
    CyclicPair.proper_pair_point_root_classes h hcomm hbeta ht hproper
  have hzY : z ∈ Y := hKY (minimalLocalFailureProperPair_distinguished_mem H z beta t)
  have hzD : z ∈ involutionPointClass z := ⟨1, by simp [rightConjugateElem]⟩
  ext s
  constructor
  · rintro ⟨hsD, hsY⟩
    obtain ⟨a, ha⟩ := subgroup_class_conjugate_mem_point h.local_datum S hzS hzcenter Y hzY hsD hsY
    have hs'D : (a : G)⁻¹ * s * a ∈ involutionPointClass z := conj_mem_pointClass hsD a
    have hs'Q : (a : G)⁻¹ * s * a ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} := by
      rw [← class_inter_point h.local_datum hQclass]
      exact ⟨hs'D, ha⟩
    rw [hQclass, hclasses] at hs'Q
    obtain ⟨m, hm⟩ := hs'Q
    have hmY : (m : G) ∈ Y := hKY m.2.2
    refine ⟨⟨(m : G) * (a : G)⁻¹, Y.mul_mem hmY (Y.inv_mem a.2)⟩, ?_⟩
    calc ((m : G) * (a : G)⁻¹)⁻¹ * z * ((m : G) * (a : G)⁻¹) =
        (a : G) * ((m : G)⁻¹ * z * m) * (a : G)⁻¹ := by group
      _ = s := by rw [hm]; group
  · rintro ⟨y, rfl⟩
    exact ⟨conj_mem_pointClass hzD y, Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) hzY) y.2⟩

theorem pair_hull_le_class_hull {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {Y : Subgroup G} (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y) :
    minimalLocalFailureProperPairHull H z beta t ≤ Subgroup.closure (conjugacyWithin Y z) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hgen := (involution_point_pair_generated_subgroup_hull h.local_datum S hzS hzcenter beta
    hbeta t ht).2.2.2.2.1
  rw [← minimalLocalFailureProperPairHull_eq_native] at hgen
  conv_lhs => rw [hgen]
  apply Subgroup.closure_mono
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k, hKY k.2⟩, rfl⟩

theorem overgroup_hull_structure {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    {L : Subgroup G} (hL : L = Subgroup.closure (conjugacyWithin Y z)) :
    conjugacyWithin Y z = conjugacyWithin L z ∧
      minimalLocalFailureProperPairHull H z beta t ≤ L ∧
      minimalLocalFailurePairActionPointHull H z ≤ L ∧ Group.IsPerfect L ∧ 2 ≤ twoRank L ∧
      fusionStronglyEmbedded (H.subgroupOf L) ∧
      CFSG.oddCore L ≤ Subgroup.center L ∧ CFSG.oddCore L ≤ H.subgroupOf L ∧
      fusionIsBenderGroup (L ⧸ CFSG.oddCore L) ∧
      Nat.card {x : L | x ∈ H.subgroupOf L ∧ orderOf x = 2} =
        Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 ∧
      {ω : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
        {ω : rightCosetSpace H | ∃ l ∈ L, rightCosetTranslate H (rightCosetMk H 1) l = ω} := by
  subst hL
  obtain ⟨hQH, hQK, -, hQ, -, hQ4, hzQ⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨hQclass, hclasses, -⟩ :=
    CyclicPair.proper_pair_point_root_classes h hcomm hbeta ht hproper
  have hzY : z ∈ Y := hKY (minimalLocalFailureProperPair_distinguished_mem H z beta t)
  have htY : t ∈ Y := hKY (minimalLocalFailureProperPair_flip_mem H z beta t)
  have hYH : ¬ Y ≤ H := fun hYH => pair_flip_not_mem_point hbeta ht (hYH htY)
  have hKL := pair_hull_le_class_hull h hbeta ht hKY
  have hQL := hQK.trans hKL
  obtain ⟨hrank, hstrong, hclass, -, -, -, hcenter, hcoreM, -, hmodel, horbit⟩ :=
    FixedPointModel.class_hull_rank_two h hcomm hsmallerR1 hY hzY hYH hQ hQ4 hQL
  have hzL : z ∈ Subgroup.closure (conjugacyWithin Y z) := distinguished_mem_properHull Y z
  have hzD : z ∈ involutionPointClass z := ⟨1, by simp [rightConjugateElem]⟩
  have hQclassL : ∀ v ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1},
      v ∈ conjugacyWithin (Subgroup.closure (conjugacyWithin Y z)) z := by
    intro v hv
    rw [hQclass, hclasses] at hv
    obtain ⟨m, rfl⟩ := hv
    exact ⟨⟨m, hKL m.2.2⟩, rfl⟩
  have hperfect : Group.IsPerfect (Subgroup.closure (conjugacyWithin Y z)) := by
    obtain ⟨w, hwQ, hw1, hwz⟩ := exists_mem_ne_ne (le_trans (by norm_num) hQ4) 1 z
    have hzw1 : z * w ≠ 1 := by
      intro hzw
      apply hwz
      have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two
        h.local_datum.distinguished_order
      calc w = z * (z * w) := by rw [← mul_assoc, hzz, one_mul]
        _ = z := by rw [hzw, mul_one]
    exact isPerfect_of_class_closure hzL (congrArg Subgroup.closure hclass)
      (hQclassL w ⟨hwQ, hw1⟩) (hQclassL (z * w) ⟨Subgroup.mul_mem _ hzQ hwQ, hzw1⟩)
  have hinvM : Nat.card {x : Subgroup.closure (conjugacyWithin Y z) |
      x ∈ H.subgroupOf (Subgroup.closure (conjugacyWithin Y z)) ∧ orderOf x = 2} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 := by
    rw [← card_diff_one (minimalLocalFailurePairActionPointHull H z)]
    let zL : Subgroup.closure (conjugacyWithin Y z) := ⟨z, hzL⟩
    have hzM : zL ∈ H.subgroupOf (Subgroup.closure (conjugacyWithin Y z)) :=
      h.local_datum.distinguished_mem
    have hzinv : IsInvolution zL := by
      have hz2 : orderOf zL = 2 :=
        (Subgroup.orderOf_mk z hzL).trans h.local_datum.distinguished_order
      exact ⟨(orderOf_eq_prime_iff.mp hz2).2, (orderOf_eq_prime_iff.mp hz2).1⟩
    have hforward : ∀ x : Subgroup.closure (conjugacyWithin Y z),
        x ∈ H.subgroupOf (Subgroup.closure (conjugacyWithin Y z)) → orderOf x = 2 →
        (x : G) ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} := by
      intro x hxM hx2
      have hxinv : IsInvolution x :=
        ⟨(orderOf_eq_prime_iff.mp hx2).2, (orderOf_eq_prime_iff.mp hx2).1⟩
      obtain ⟨g, -, hg⟩ := IsStronglyEmbedded.involutions_conjugate_in
        (fusionStronglyEmbedded.to_native hstrong) hzM hzinv hxM hxinv
      have hxD : (x : G) ∈ involutionPointClass z := by
        rw [← hg]
        exact conj_mem_pointClass hzD (g : G)
      rw [← class_inter_point h.local_datum hQclass]
      exact ⟨hxD, hxM⟩
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨((x : Subgroup.closure (conjugacyWithin Y z)) : G),
      hforward x x.2.1 x.2.2⟩) ⟨?_, ?_⟩
    · intro x y hxy
      have h' := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨w, hw⟩
      have hwD : w ∈ involutionPointClass z := point_subgroup_class h.local_datum hQclass hw
      refine ⟨⟨⟨w, hQL hw.1⟩, hQH hw.1, ?_⟩, rfl⟩
      exact (Subgroup.orderOf_mk w (hQL hw.1)).trans
        (order_two_of_mem_pointClass h.local_datum.distinguished_order hwD)
  exact ⟨hclass, hKL, hQL, hperfect, hrank, hstrong, hcenter, hcoreM, hmodel, hinvM, horbit⟩

end CFSG.ShultStronglyClosedTI.OvergroupHull
