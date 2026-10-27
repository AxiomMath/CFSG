module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeCosets
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type} [Group G] [Finite G]

theorem subgroup_class_member_inheritance {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hcentral : InvolutionPointCentralSylow z)
    {Q : Subgroup G} (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {Y : Subgroup G}
    (hYH : ¬ Y ≤ H) {r : G} (hr : r ∈ Q ⊓ Y) (hr1 : r ≠ 1)
    (hEclass : ((Q ⊓ Y : Subgroup G) : Set G) \ {1} ⊆ conjugacyWithin Y r) :
    InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hr.2⟩ : Y) ∧
      InvolutionPointCentralSylow (⟨r, hr.2⟩ : Y) ∧
      involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y r ∧
      Q ⊓ Y ≤ Subgroup.closure (conjugacyWithin Y r) := by
  have hrQ : r ∈ (Q : Set G) \ {1} := ⟨hr.1, hr1⟩
  have hrc : r ∈ conjugacyWithin H z := hQclass ▸ hrQ
  obtain ⟨k, hk⟩ := hrc
  have hkr : rightConjugateElem z (k : G) = r := hk
  have hdatum : InvolutionPointLocalEmbedding H r := by
    have hl := local_point_datum_right_conjugate h (k : G)
    rwa [minimalLocalFailure_point_right_conjugate H k k.2, hkr] at hl
  have hcentr : InvolutionPointCentralSylow r := by
    have hc := minimalLocalFailure_central_sylow_right_conjugate hcentral (k : G)
    rwa [hkr] at hc
  obtain ⟨hlocal, hsylow⟩ := involution_point_subgroup_inheritance hdatum Y hr.2 hYH
  have hrD : r ∈ involutionPointClass z := point_subgroup_class h hQclass hrQ
  have hDr : involutionPointClass r = involutionPointClass z := pointClass_eq_of_mem hrD
  have hrY : r ∈ Y := hr.2
  have hDY : involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y r := by
    obtain ⟨S, hrS, hrcenter⟩ := hcentr
    ext s
    constructor
    · rintro ⟨hsD, hsY⟩
      obtain ⟨a, ha⟩ := subgroup_class_conjugate_mem_point hdatum S hrS hrcenter Y hrY
        (hDr.symm ▸ hsD) hsY
      have hs'D : (a : G)⁻¹ * s * a ∈ involutionPointClass z := conj_mem_pointClass hsD a
      have hs'Y : (a : G)⁻¹ * s * a ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem a.2) hsY) a.2
      have hs'Q : (a : G)⁻¹ * s * a ∈ (Q : Set G) \ {1} := by
        rw [← class_inter_point h hQclass]
        exact ⟨hs'D, ha⟩
      obtain ⟨y, hy⟩ := hEclass ⟨⟨hs'Q.1, hs'Y⟩, hs'Q.2⟩
      refine ⟨y * a⁻¹, ?_⟩
      calc
        ((y * a⁻¹ : Y) : G)⁻¹ * r * ((y * a⁻¹ : Y) : G) =
            (a : G) * ((y : G)⁻¹ * r * y) * (a : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        _ = s := by
          rw [hy]
          group
    · rintro ⟨y, rfl⟩
      refine ⟨conj_mem_pointClass hrD y, ?_⟩
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) hrY) y.2
  refine ⟨hlocal, hsylow hcentr, hDY, ?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (hEclass ⟨hw, hw1⟩)

theorem subgroup_class_data {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z) {Q : Subgroup G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {Y : Subgroup G}
    (hYH : ¬ Y ≤ H) {X₀ : Subgroup G} (hX₀ : X₀ ≤ H ⊓ Y)
    (htrans : ∀ a ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1}, ∃ x ∈ X₀, x⁻¹ * a * x = b)
    {r : G} (hr : r ∈ Q ⊓ Y) (hr1 : r ≠ 1) :
    InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hr.2⟩ : Y) ∧
      InvolutionPointCentralSylow (⟨r, hr.2⟩ : Y) ∧
      involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y r ∧
      Q ⊓ Y ≤ Subgroup.closure (conjugacyWithin Y r) ∧
      conjugacyWithin (H ⊓ Y) r = ((Q ⊓ Y : Subgroup G) : Set G) \ {1} := by
  have hEclass : ((Q ⊓ Y : Subgroup G) : Set G) \ {1} ⊆ conjugacyWithin Y r := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := htrans r ⟨hr, hr1⟩ w hw
    exact ⟨⟨x, (hX₀ hx).2⟩, hxw⟩
  obtain ⟨hlocal, hsylow, hDY, hEL⟩ :=
    subgroup_class_member_inheritance h hcentral hQclass hYH hr hr1 hEclass
  refine ⟨hlocal, hsylow, hDY, hEL, ?_⟩
  ext w
  constructor
  · rintro ⟨k, rfl⟩
    have hrQ : r ∈ Q := hr.1
    refine ⟨⟨point_subgroup_normalized hQclass k k.2.1 r hrQ, ?_⟩, conj_ne_one hr1⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem k.2.2) hr.2) k.2.2
  · intro hw
    obtain ⟨x, hx, hxw⟩ := htrans r ⟨hr, hr1⟩ w hw
    exact ⟨⟨x, hX₀ hx⟩, hxw⟩

theorem subgroup_two_transitive {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hcentral : InvolutionPointCentralSylow z)
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {Y : Subgroup G} (hYH : ¬ Y ≤ H) {X₀ : Subgroup G} (hX₀ : X₀ ≤ H ⊓ Y)
    (htrans : ∀ a ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1}, ∃ x ∈ X₀, x⁻¹ * a * x = b)
    {r : G} (hr : r ∈ Q ⊓ Y) (hr1 : r ≠ 1) (hE : 2 < Nat.card (Q ⊓ Y : Subgroup G)) :
    let Δ := CyclicSemiregular.baseOrbit H Y
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
      ∃ g ∈ Y, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d := by
  intro Δ
  obtain ⟨hlocal, hsylow, -, -, hclassY⟩ :=
    subgroup_class_data h hcentral hQclass hYH hX₀ htrans hr hr1
  obtain ⟨S₂, hrS, hrcenter⟩ := hsylow
  have hQH : Q ≤ H := point_subgroup_le h.distinguished_mem hQclass
  have hQHY : Q.subgroupOf Y ≤ H.subgroupOf Y := fun x hx => hQH hx
  have hQnormal : ((Q.subgroupOf Y).subgroupOf (H.subgroupOf Y)).Normal := by
    constructor
    intro n hn g
    have hn' : (((n : H.subgroupOf Y) : Y) : G) ∈ Q := hn
    change (((g : H.subgroupOf Y) : Y) : G) * (((n : H.subgroupOf Y) : Y) : G) *
      (((g : H.subgroupOf Y) : Y) : G)⁻¹ ∈ Q
    have hmem := point_subgroup_normalized hQclass ((((g : H.subgroupOf Y) : Y) : G))⁻¹
      (H.inv_mem g.2) _ hn'
    rwa [inv_inv] at hmem
  have hQtwo : IsPGroup 2 (Q.subgroupOf Y) := by
    intro g
    obtain ⟨k, hk⟩ := hQ2 ⟨((g : Y) : G), g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hrQ : (⟨r, hr.2⟩ : Y) ∈ Q.subgroupOf Y := hr.1
  obtain ⟨-, -, htwo⟩ :=
    CFSG.ProperTwoGeneratedCore.local_involution_point_normal_two_hull_sylow_fixed_points
      hlocal S₂ hrS hrcenter hQHY hQnormal hQtwo hrQ
  have hm : Nat.card (conjugacyWithin (H.subgroupOf Y) (⟨r, hr.2⟩ : Y)) =
      Nat.card (Q ⊓ Y : Subgroup G) - 1 := by
    rw [CyclicSemiregular.card_conjugacyWithin_subgroupOf]
    change Nat.card (conjugacyWithin (H ⊓ Y) r) = _
    rw [hclassY, card_diff_one]
  let ι := restrictedRightCosetEmbedding H Y
  have hrange : Set.range ι = Δ := CyclicSemiregular.range_restrictedRightCosetEmbedding H Y
  have hmemΔ : ∀ ω ∈ Δ, ∃ ω', ι ω' = ω := fun ω hω => by
    rw [← hrange] at hω
    exact hω
  intro a ha b hb c hc d hd hab hcd
  have h1 : 1 < Nat.card (conjugacyWithin (H.subgroupOf Y) (⟨r, hr.2⟩ : Y)) := by
    rw [hm]
    omega
  obtain ⟨a', rfl⟩ := hmemΔ a ha
  obtain ⟨b', rfl⟩ := hmemΔ b hb
  obtain ⟨c', rfl⟩ := hmemΔ c hc
  obtain ⟨d', rfl⟩ := hmemΔ d hd
  obtain ⟨g, hg1, hg2⟩ := htwo h1 a' b' c' d' (fun h' => hab (congrArg ι h'))
    (fun h' => hcd (congrArg ι h'))
  refine ⟨g, g.2, ?_, ?_⟩
  · rw [← CyclicSemiregular.restrictedRightCosetEmbedding_translate,
      ← pointRightCosetMul_eq_translate, hg1]
  · rw [← CyclicSemiregular.restrictedRightCosetEmbedding_translate,
      ← pointRightCosetMul_eq_translate, hg2]

end CFSG.ShultStronglyClosedTI.CoprimePrime
