module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem ambient_two_transitive {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z) {Q : Subgroup G}
    (hQ : CFSG.Open.IsElemAbelian 2 Q) (hQ4 : 4 ≤ Nat.card Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) :
    ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d := by
  obtain ⟨S, hzS, hzcenter⟩ := hcentral
  have hQH : Q ≤ H := point_subgroup_le h.distinguished_mem hQclass
  have hQnorm := point_subgroup_normalized hQclass
  have hQnormal : (Q.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmem := hQnorm ((g : G))⁻¹ (H.inv_mem g.2) _ hn
    simpa only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  have hzQ : z ∈ Q := by
    have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
    rw [← hQclass] at hz
    exact hz.1
  have hQp : IsPGroup 2 Q := fun x =>
    ⟨1, by simpa only [pow_one] using Subtype.ext (hQ.2 x x.2)⟩
  obtain ⟨-, -, htwo⟩ :=
    CFSG.ProperTwoGeneratedCore.local_involution_point_normal_two_hull_sylow_fixed_points
      h S hzS hzcenter hQH hQnormal hQp hzQ
  have hm1 : 1 < Nat.card (conjugacyWithin H z) := by
    rw [← hQclass, card_diff_one]
    omega
  intro a b c d hab hcd
  obtain ⟨g, h1, h2⟩ := htwo hm1 a b c d hab hcd
  rw [pointRightCosetMul_eq_translate] at h1 h2
  exact ⟨g, h1, h2⟩

omit [Finite G] in
theorem class_inter_point_eq {H : Subgroup G} {u : G} (huH : u ∈ H)
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}) :
    involutionPointClass u ∩ (H : Set G) = conjugacyWithin H u := by
  ext x
  constructor
  · rintro ⟨⟨g, rfl⟩, hx⟩
    have hfix : rightCosetTranslate H (rightCosetMk H g⁻¹) u = rightCosetMk H g⁻¹ := by
      apply (translate_mk_fixed_iff H g⁻¹ u).mpr
      rw [inv_inv]
      exact hx
    have hmem : rightCosetMk H g⁻¹ ∈ {omega : rightCosetSpace H |
        ∃ y ∈ Subgroup.centralizer ({u} : Set G),
          rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
      rw [horbit]
      exact hfix
    obtain ⟨y, hy, hyg⟩ := hmem
    rw [translate_base_mk, rightCosetMk_eq_iff] at hyg
    have hyu : y⁻¹ * u * y = u := by
      rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hy, inv_mul_cancel_left]
    refine ⟨⟨y * g, ?_⟩, ?_⟩
    · have hmem' := H.inv_mem hyg
      rwa [mul_inv_rev, inv_inv, inv_inv] at hmem'
    · change (y * g)⁻¹ * u * (y * g) = g⁻¹ * u * g
      rw [show (y * g)⁻¹ * u * (y * g) = g⁻¹ * (y⁻¹ * u * y) * g by group, hyu]
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, rfl⟩, H.mul_mem (H.mul_mem (H.inv_mem k.2) huH) k.2⟩

theorem not_mem_pointClass_of_two_fixed {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {u : G} (huB : u ∈ pairPointStabilizer H beta) :
    u ∉ involutionPointClass z := by
  intro huD
  have hα : rightCosetTranslate H (rightCosetMk H 1) u = rightCosetMk H 1 :=
    (mem_rightCosetStabilizer_iff H _ u).mp huB.1
  have hβ : rightCosetTranslate H beta u = beta := (mem_rightCosetStabilizer_iff H _ u).mp huB.2
  exact hbeta (class_fixed_unique h huD hβ hα)

omit [Finite G] in
theorem exists_conj_mem_pairPointStabilizer {H : Subgroup G}
    (htwo : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1) {v : G} (hvH : v ∈ H)
    {γ : rightCosetSpace H} (hγ : γ ≠ rightCosetMk H 1)
    (hγv : rightCosetTranslate H γ v = γ) :
    ∃ g ∈ H, g * v * g⁻¹ ∈ pairPointStabilizer H beta := by
  obtain ⟨g, hgα, hgβ⟩ :=
    htwo (rightCosetMk H 1) beta (rightCosetMk H 1) γ hbeta.symm hγ.symm
  have hgH : g ∈ H := (translate_base_iff H g).mp hgα
  refine ⟨g, hgH, (mem_rightCosetStabilizer_iff H _ _).mpr ?_,
    (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
  · exact (translate_base_iff H _).mpr (H.mul_mem (H.mul_mem hgH hvH) (H.inv_mem hgH))
  · rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hgβ, hγv, ← hgβ,
      rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]

omit [Finite G] in
theorem conj_mem_point_subgroup_of_fixed {H Q : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {s : G}
    (hs : s ∈ involutionPointClass z) {g : G}
    (hfix : rightCosetTranslate H (rightCosetMk H g) s = rightCosetMk H g) :
    g * s * g⁻¹ ∈ Q := by
  have hsH : g * s * g⁻¹ ∈ H := (translate_mk_fixed_iff H g s).mp hfix
  have hsD : g * s * g⁻¹ ∈ involutionPointClass z := by
    simpa only [inv_inv] using conj_mem_pointClass hs g⁻¹
  have hsQ : g * s * g⁻¹ ∈ (Q : Set G) \ {1} := by
    rw [← class_inter_point h hQclass]
    exact ⟨hsD, hsH⟩
  exact hsQ.1

omit [Finite G] in
theorem commute_conj_point_subgroup {H Q : Subgroup G} {z : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G}
    (hQu : Q ≤ Subgroup.centralizer ({u} : Set G))
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega})
    {v : G} (hv : v ∈ involutionPointClass u) {g : G}
    (hfix : rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g) {q : G}
    (hq : q ∈ Q) : Commute v (g⁻¹ * q * g) := by
  obtain ⟨x, rfl⟩ := hv
  change rightCosetTranslate H (rightCosetMk H g) (x⁻¹ * u * x) = rightCosetMk H g at hfix
  have hfix' : rightCosetTranslate H (rightCosetMk H (g * x⁻¹)) u = rightCosetMk H (g * x⁻¹) := by
    apply (translate_mk_fixed_iff H _ u).mpr
    have hmem := (translate_mk_fixed_iff H g _).mp hfix
    rwa [show g * (x⁻¹ * u * x) * g⁻¹ = g * x⁻¹ * u * (g * x⁻¹)⁻¹ by group] at hmem
  have hmem : rightCosetMk H (g * x⁻¹) ∈ {omega : rightCosetSpace H |
      ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
    rw [horbit]
    exact hfix'
  obtain ⟨y, hy, hyg⟩ := hmem
  rw [translate_base_mk, rightCosetMk_eq_iff] at hyg
  set k := g * x⁻¹ * y⁻¹ with hk
  have hgk : g = k * y * x := by rw [hk]; group
  have hq' : k⁻¹ * q * k ∈ Q := point_subgroup_normalized hQclass k hyg q hq
  have huq : Commute u (k⁻¹ * q * k) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hQu hq')).symm
  have huy : Commute u y := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hcomm : Commute u (y⁻¹ * (k⁻¹ * q * k) * y) :=
    (huy.inv_right.mul_right huq).mul_right huy
  have hconj : g⁻¹ * q * g = x⁻¹ * (y⁻¹ * (k⁻¹ * q * k) * y) * x := by
    rw [hgk]
    group
  rw [hconj]
  change Commute (x⁻¹ * u * x) (x⁻¹ * (y⁻¹ * (k⁻¹ * q * k) * y) * x)
  simpa only [inv_inv] using hcomm.conj x⁻¹

theorem mul_mem_of_coset_mem {H Q : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G}
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega})
    {W : Set G} (hW : ∀ x ∈ W, ∀ g : G, g⁻¹ * x * g ∈ W)
    (hcoset : ∀ e ∈ ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1},
      u * e ∈ W)
    {v r : G} (hv : v ∈ involutionPointClass u) (hr : r ∈ involutionPointClass z)
    (hvr : Commute v r) : v * r ∈ W := by
  obtain ⟨x, rfl⟩ := hv
  change Commute (x⁻¹ * u * x) r at hvr
  set r' := x * r * x⁻¹ with hr'
  have hr'D : r' ∈ involutionPointClass z := by
    simpa only [inv_inv] using conj_mem_pointClass hr x⁻¹
  have hr'u : Commute r' u := by
    have hc := (hvr.conj x).symm
    rwa [show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at hc
  obtain ⟨γ, hγ⟩ := class_fixed_exists h hr'D
  have hγu : rightCosetTranslate H γ u = γ := class_fixed_of_commute h hr'D hr'u hγ
  have hγmem : γ ∈ {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
      rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
    rw [horbit]
    exact hγu
  obtain ⟨y, hy, hyγ⟩ := hγmem
  set r'' := y * r' * y⁻¹ with hr''
  have hr''D : r'' ∈ involutionPointClass z := by
    simpa only [inv_inv] using conj_mem_pointClass hr'D y⁻¹
  have hr''H : r'' ∈ H := by
    apply (translate_base_iff H _).mp
    rw [hr'', ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hyγ, hγ, ← hyγ,
      rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hr''Q : r'' ∈ (Q : Set G) \ {1} := by
    rw [← class_inter_point h hQclass]
    exact ⟨hr''D, hr''H⟩
  have huy : Commute u y := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hyu : y * u * y⁻¹ = u := by rw [← huy.eq, mul_inv_cancel_right]
  have hr''u : Commute r'' u := by
    have hc := hr'u.conj y
    rwa [hyu] at hc
  have hmem := hcoset r'' ⟨⟨hr''Q.1, Subgroup.mem_centralizer_singleton_iff.mpr hr''u.eq⟩,
    hr''Q.2⟩
  have hfinal := hW _ hmem (y * x)
  rwa [show (y * x)⁻¹ * (u * r'') * (y * x) = x⁻¹ * (y⁻¹ * u * y) * x * r by
    rw [hr'', hr']; group, show y⁻¹ * u * y = u by rw [mul_assoc, huy.eq,
      inv_mul_cancel_left]] at hfinal

end CFSG.ShultStronglyClosedTI.MixedClass
