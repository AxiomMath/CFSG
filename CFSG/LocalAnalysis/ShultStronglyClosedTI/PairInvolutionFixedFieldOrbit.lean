module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldAlgebra
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public section

namespace CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (x g : G) : orderOf (g⁻¹ * x * g) = orderOf x :=
  (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * x = g⁻¹ * x * g * g⁻¹ by group)).symm

theorem conj_mem_pointClass {z s : G} (hs : s ∈ involutionPointClass z) (g : G) :
    g⁻¹ * s * g ∈ involutionPointClass z := by
  obtain ⟨k, rfl⟩ := hs
  exact ⟨k * g, by simp only [rightConjugateElem, mul_inv_rev, mul_assoc]⟩

theorem exists_rightCosetMk {H : Subgroup G} (omega : rightCosetSpace H) :
    ∃ g : G, rightCosetMk H g = omega :=
  Quotient.exists_rep omega

theorem rightCosetMk_eq_iff (H : Subgroup G) (a b : G) :
    rightCosetMk H a = rightCosetMk H b ↔ b * a⁻¹ ∈ H := by
  unfold rightCosetMk
  rw [Quotient.eq, QuotientGroup.rightRel_apply]

theorem translate_base_iff (H : Subgroup G) (g : G) :
    rightCosetTranslate H (rightCosetMk H 1) g = rightCosetMk H 1 ↔ g ∈ H := by
  rw [← mem_rightCosetStabilizer_iff, rightCosetStabilizer_base]

theorem translate_mk_fixed_iff (H : Subgroup G) (x g : G) :
    rightCosetTranslate H (rightCosetMk H x) g = rightCosetMk H x ↔ x * g * x⁻¹ ∈ H := by
  rw [rightCosetTranslate_mk, rightCosetMk_eq_iff, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem translate_base_mk (H : Subgroup G) (y : G) :
    rightCosetTranslate H (rightCosetMk H 1) y = rightCosetMk H y := by
  rw [rightCosetTranslate_mk, one_mul]

theorem class_fixed_exists [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {s : G} (hs : s ∈ involutionPointClass z) :
    ∃ omega : rightCosetSpace H, rightCosetTranslate H omega s = omega := by
  obtain ⟨omega, homega, _⟩ :=
    ((involution_point_unique_containment_action h.distinguished_mem
      h.distinguished_order).2 h.unique_containment).2.1 s hs
  exact ⟨omega, (pointRightCosetMul_eq_translate H omega s).symm.trans homega⟩

theorem class_fixed_unique [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {s : G} (hs : s ∈ involutionPointClass z)
    {omega₁ omega₂ : rightCosetSpace H} (h₁ : rightCosetTranslate H omega₁ s = omega₁)
    (h₂ : rightCosetTranslate H omega₂ s = omega₂) : omega₁ = omega₂ := by
  obtain ⟨omega, _, huniq⟩ :=
    ((involution_point_unique_containment_action h.distinguished_mem
      h.distinguished_order).2 h.unique_containment).2.1 s hs
  rw [huniq omega₁ ((pointRightCosetMul_eq_translate H omega₁ s).trans h₁),
    huniq omega₂ ((pointRightCosetMul_eq_translate H omega₂ s).trans h₂)]

theorem class_fixed_of_commute [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {s : G} (hs : s ∈ involutionPointClass z)
    {w : G} (hsw : Commute s w) {omega : rightCosetSpace H}
    (homega : rightCosetTranslate H omega s = omega) :
    rightCosetTranslate H omega w = omega := by
  apply class_fixed_unique h hs _ homega
  rw [rightCosetTranslate_mul, ← hsw.eq, ← rightCosetTranslate_mul, homega]

theorem point_subgroup_le {H Q : Subgroup G} {z : G} (hz : z ∈ H)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) : Q ≤ H := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact H.one_mem
  · have hvc : v ∈ conjugacyWithin H z := hQclass ▸ (⟨hv, hv1⟩ : v ∈ (Q : Set G) \ {1})
    obtain ⟨k, rfl⟩ := hvc
    exact H.mul_mem (H.mul_mem (H.inv_mem k.2) hz) k.2

theorem point_subgroup_normalized {H Q : Subgroup G} {z : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) :
    ∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q := by
  intro k hk v hv
  by_cases hv1 : v = 1
  · rw [hv1, mul_one, inv_mul_cancel]
    exact Q.one_mem
  · have hvc : v ∈ conjugacyWithin H z := hQclass ▸ (⟨hv, hv1⟩ : v ∈ (Q : Set G) \ {1})
    obtain ⟨a, rfl⟩ := hvc
    have hmem : k⁻¹ * ((a : G)⁻¹ * z * a) * k ∈ conjugacyWithin H z :=
      ⟨a * ⟨k, hk⟩, by simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]⟩
    rw [← hQclass] at hmem
    exact hmem.1

theorem class_inter_point {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) :
    involutionPointClass z ∩ (H : Set G) = (Q : Set G) \ {1} := by
  rw [pointClass_inter_eq_subgroupClass h, hQclass]
  ext t
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩

theorem point_subgroup_class {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {v : G} (hv : v ∈ (Q : Set G) \ {1}) :
    v ∈ involutionPointClass z := by
  rw [← class_inter_point h hQclass] at hv
  exact hv.1

theorem exists_commuting_flip [Finite G] {H : Subgroup G} {z : G} (hz : orderOf z = 2)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (htB : conjugacyWithin (pairPointStabilizer H beta) t = (fun x => t * x) '' (X : Set G))
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    ∃ tu ∈ (fun x => t * x) '' (X : Set G), Commute tu u ∧
      tu ∈ rightPairFlipFiber H z beta ∧ rightCosetTranslate H beta tu = rightCosetMk H 1 := by
  let B := pairPointStabilizer H beta
  let F := conjugacyWithin B t
  have hFmem : ∀ s ∈ F, u⁻¹ * s * u ∈ F := by
    rintro s ⟨b, rfl⟩
    exact ⟨b * ⟨u, huB⟩, by simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]⟩
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  let f : F → F := fun s => ⟨u⁻¹ * s * u, hFmem s s.2⟩
  have hf : Function.Involutive f := by
    intro s
    apply Subtype.ext
    change u⁻¹ * (u⁻¹ * s * u) * u = s
    calc
      u⁻¹ * (u⁻¹ * (s : G) * u) * u = (u * u)⁻¹ * s * (u * u) := by group
      _ = s := by rw [huu, inv_one, one_mul, mul_one]
  have hFcard : Nat.card F = Nat.card X := by
    change Nat.card ↥(conjugacyWithin B t) = Nat.card X
    rw [htB]
    exact Nat.card_image_of_injective (mul_right_injective t) _
  obtain ⟨s, hs⟩ := exists_fixed_of_involutive hf (hFcard ▸ hXodd)
  have hsfix : u⁻¹ * (s : G) * u = s := congrArg Subtype.val hs
  have hsX : (s : G) ∈ (fun x => t * x) '' (X : Set G) := by
    have hsF : (s : G) ∈ conjugacyWithin B t := s.2
    rwa [htB] at hsF
  obtain ⟨b, hb⟩ := s.2
  have hbα : rightCosetTranslate H (rightCosetMk H 1) (b : G) = rightCosetMk H 1 :=
    (mem_rightCosetStabilizer_iff H _ _).mp b.2.1
  have hbβ : rightCosetTranslate H beta (b : G) = beta :=
    (mem_rightCosetStabilizer_iff H _ _).mp b.2.2
  have hbinvα : rightCosetTranslate H (rightCosetMk H 1) (b : G)⁻¹ = rightCosetMk H 1 := by
    conv_lhs => rw [← hbα]
    rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hsα : rightCosetTranslate H (rightCosetMk H 1) (s : G) = beta := by
    rw [← hb, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hbinvα, ht.2, hbβ]
  have hsclass : (s : G) ∈ involutionPointClass z := by
    rw [← hb]
    exact conj_mem_pointClass ht.1 b
  have hss : (s : G) * s = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (order_two_of_mem_pointClass hz hsclass)
  refine ⟨s, hsX, ?_, ⟨hsclass, hsα⟩, ?_⟩
  · change (s : G) * u = u * s
    have h' := congrArg (fun x : G => u * x) hsfix
    simpa only [mul_assoc, mul_inv_cancel_left] using h'
  · rw [← hsα, rightCosetTranslate_mul, hss, rightCosetTranslate_one]

theorem centralizer_proper_escape (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} {u tu : G} (hu : orderOf u = 2)
    (htu : Commute tu u) (htuH : tu ∉ H) :
    Subgroup.centralizer ({u} : Set G) ≠ ⊤ ∧ ¬ Subgroup.centralizer ({u} : Set G) ≤ H := by
  refine ⟨?_, fun hle => htuH (hle (Subgroup.mem_centralizer_singleton_iff.mpr htu.eq))⟩
  intro htop
  have hcenter : u ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (self := hsimple) (Subgroup.center G)
    with hbot | htop'
  · rw [hbot, Subgroup.mem_bot] at hcenter
    rw [hcenter, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · obtain ⟨a, b, hab⟩ := hnonab
    have hb : b ∈ Subgroup.center G := by
      rw [htop']
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

end CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
