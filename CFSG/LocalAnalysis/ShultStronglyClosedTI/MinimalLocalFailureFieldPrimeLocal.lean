module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeCosets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldClass

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

universe u

variable {G : Type u} [Group G] [Finite G]

theorem centralizer_class_data {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hcentral : InvolutionPointCentralSylow z) {Q : Subgroup G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {y : G}
    (hYH : ¬ Subgroup.centralizer ({y} : Set G) ≤ H) {X₀ : Subgroup G}
    (hX₀ : X₀ ≤ H ⊓ Subgroup.centralizer ({y} : Set G))
    (htrans : ∀ a ∈ ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) \ {1},
        ∃ x ∈ X₀, x⁻¹ * a * x = b)
    {r : G} (hr : r ∈ Q ⊓ Subgroup.centralizer ({y} : Set G)) (hr1 : r ≠ 1) :
    let Y := Subgroup.centralizer ({y} : Set G)
    let E := Q ⊓ Y
    InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hr.2⟩ : Y) ∧
      InvolutionPointCentralSylow (⟨r, hr.2⟩ : Y) ∧
      involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y r ∧
      E ≤ Subgroup.closure (conjugacyWithin Y r) ∧
      conjugacyWithin (H ⊓ Y) r = (E : Set G) \ {1} := by
  intro Y E
  have hEclass : (E : Set G) \ {1} ⊆ conjugacyWithin Y r := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := htrans r ⟨hr, hr1⟩ w hw
    exact ⟨⟨x, (hX₀ hx).2⟩, hxw⟩
  obtain ⟨hlocal, hsylow, hDY, hEL⟩ :=
    class_member_inheritance h hcentral hQclass hYH hr hr1 hEclass
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

omit [Finite G] in
theorem centralizer_baseOrbit_basic {H : Subgroup G} {z : G}
    {beta : rightCosetSpace H} {y : G} (hyH : y ∈ H) {ty : G}
    (hty : ty ∈ rightPairFlipFiber H z beta) (htyY : Commute ty y) :
    let Y := Subgroup.centralizer ({y} : Set G)
    rightCosetMk H 1 ∈ baseOrbit H Y ∧ beta ∈ baseOrbit H Y ∧
      baseOrbit H Y ⊆ {omega | rightCosetTranslate H omega y = omega} := by
  intro Y
  refine ⟨⟨1, Y.one_mem, rightCosetTranslate_one H _⟩,
    ⟨ty, Subgroup.mem_centralizer_singleton_iff.mpr htyY.eq, hty.2⟩, ?_⟩
  rintro omega ⟨g, hg, rfl⟩
  change rightCosetTranslate H (rightCosetTranslate H (rightCosetMk H 1) g) y =
    rightCosetTranslate H (rightCosetMk H 1) g
  rw [rightCosetTranslate_mul, Subgroup.mem_centralizer_singleton_iff.mp hg,
    ← rightCosetTranslate_mul, (translate_base_iff H y).mpr hyH]

theorem centralizer_normal_two_hull {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hcentral : InvolutionPointCentralSylow z)
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {y : G} (hYH : ¬ Subgroup.centralizer ({y} : Set G) ≤ H) {X₀ : Subgroup G}
    (hX₀ : X₀ ≤ H ⊓ Subgroup.centralizer ({y} : Set G))
    (htrans : ∀ a ∈ ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) \ {1},
        ∃ x ∈ X₀, x⁻¹ * a * x = b)
    {r : G} (hr : r ∈ Q ⊓ Subgroup.centralizer ({y} : Set G)) (hr1 : r ≠ 1) :
    let Y := Subgroup.centralizer ({y} : Set G)
    let E := Q ⊓ Y
    let Δ := baseOrbit H Y
    (2 < Nat.card E → ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
        ∃ g ∈ Y, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card E - 1 →
        (∀ S : Sylow p Y, ∃ lam ∈ Δ, ∃ mu ∈ Δ, lam ≠ mu ∧
          pointFixedSet H ((S : Subgroup Y).map Y.subtype) ∩ Δ = {lam, mu}) ∧
        ∀ gam ∈ Δ, ∀ del ∈ Δ, gam ≠ del →
          (Nat.card (Y ⊓ (rightCosetStabilizer H gam ⊓ rightCosetStabilizer H del) :
            Subgroup G)).factorization p = (Nat.card Y).factorization p := by
  intro Y E Δ
  obtain ⟨hlocal, hsylow, -, -, hclassY⟩ :=
    centralizer_class_data h hcentral hQclass hYH hX₀ htrans hr hr1
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
  obtain ⟨-, hprime, htwo⟩ :=
    CFSG.ProperTwoGeneratedCore.local_involution_point_normal_two_hull_sylow_fixed_points
      hlocal S₂ hrS hrcenter hQHY hQnormal hQtwo hrQ
  have hm : Nat.card (conjugacyWithin (H.subgroupOf Y) (⟨r, hr.2⟩ : Y)) = Nat.card E - 1 := by
    rw [card_conjugacyWithin_subgroupOf]
    change Nat.card (conjugacyWithin (H ⊓ Y) r) = _
    rw [hclassY, card_diff_one]
  let ι := restrictedRightCosetEmbedding H Y
  have hrange : Set.range ι = Δ := range_restrictedRightCosetEmbedding H Y
  have hmemΔ : ∀ ω ∈ Δ, ∃ ω', ι ω' = ω := fun ω hω => by
    rw [← hrange] at hω
    exact hω
  have hιΔ : ∀ ω', ι ω' ∈ Δ := fun ω' => hrange ▸ ⟨ω', rfl⟩
  refine ⟨fun hE a ha b hb c hc d hd hab hcd => ?_, fun p hp hpE => ?_⟩
  · have h1 : 1 < Nat.card (conjugacyWithin (H.subgroupOf Y) (⟨r, hr.2⟩ : Y)) := by
      rw [hm]
      omega
    obtain ⟨a', rfl⟩ := hmemΔ a ha
    obtain ⟨b', rfl⟩ := hmemΔ b hb
    obtain ⟨c', rfl⟩ := hmemΔ c hc
    obtain ⟨d', rfl⟩ := hmemΔ d hd
    obtain ⟨g, hg1, hg2⟩ := htwo h1 a' b' c' d' (fun h' => hab (congrArg ι h'))
      (fun h' => hcd (congrArg ι h'))
    refine ⟨g, g.2, ?_, ?_⟩
    · rw [← restrictedRightCosetEmbedding_translate, ← pointRightCosetMul_eq_translate, hg1]
    · rw [← restrictedRightCosetEmbedding_translate, ← pointRightCosetMul_eq_translate, hg2]
  · have hpm : p ∣ Nat.card (conjugacyWithin (H.subgroupOf Y) (⟨r, hr.2⟩ : Y)) := hm ▸ hpE
    obtain ⟨hall, hpair⟩ := hprime p hp hpm
    refine ⟨fun S => ?_, fun gam hgam del hdel hne => ?_⟩
    · obtain ⟨-, lam, mu, hne, hfix⟩ := hall S
      refine ⟨ι lam, hιΔ lam, ι mu, hιΔ mu, fun h' => hne
        (restrictedRightCosetEmbedding_injective H Y h'), ?_⟩
      ext ω
      constructor
      · rintro ⟨hωfix, hωΔ⟩
        obtain ⟨ω', rfl⟩ := hmemΔ ω hωΔ
        rw [← restricted_mem_pointFixedSet_iff, hfix] at hωfix
        rcases hωfix with h' | h'
        · exact Or.inl (congrArg ι h')
        · exact Or.inr (congrArg ι h')
      · intro hω
        rcases hω with h' | h'
        · rw [h']
          refine ⟨(restricted_mem_pointFixedSet_iff H Y _ lam).mp ?_, hιΔ lam⟩
          rw [hfix]
          exact Or.inl rfl
        · rw [Set.mem_singleton_iff] at h'
          rw [h']
          refine ⟨(restricted_mem_pointFixedSet_iff H Y _ mu).mp ?_, hιΔ mu⟩
          rw [hfix]
          exact Or.inr rfl
    · obtain ⟨lam, rfl⟩ := hmemΔ gam hgam
      obtain ⟨mu, rfl⟩ := hmemΔ del hdel
      have hne' : lam ≠ mu := fun h' => hne (congrArg ι h')
      let : Fact p.Prime := ⟨hp⟩
      let P : Sylow p (rightCosetStabilizer (H.subgroupOf Y) lam ⊓
        rightCosetStabilizer (H.subgroupOf Y) mu : Subgroup Y) := default
      obtain ⟨⟨T, hT⟩, -⟩ := hpair lam mu hne' P
      have hTP : Nat.card T = Nat.card P := by
        rw [hT, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity] at hTP
      have hfact := Nat.pow_right_injective hp.two_le hTP
      have hcardK : Nat.card (rightCosetStabilizer (H.subgroupOf Y) lam ⊓
          rightCosetStabilizer (H.subgroupOf Y) mu : Subgroup Y) =
          Nat.card (Y ⊓ (rightCosetStabilizer H (ι lam) ⊓ rightCosetStabilizer H (ι mu)) :
            Subgroup G) := by
        have hinf : (Y ⊓ rightCosetStabilizer H (ι lam)) ⊓ (Y ⊓ rightCosetStabilizer H (ι mu)) =
            Y ⊓ (rightCosetStabilizer H (ι lam) ⊓ rightCosetStabilizer H (ι mu)) := by
          ext g
          simp only [Subgroup.mem_inf]
          tauto
        rw [← Subgroup.card_map_of_injective Y.subtype_injective,
          Subgroup.map_inf_eq _ _ _ Y.subtype_injective, restricted_stabilizer_map,
          restricted_stabilizer_map, hinf]
      rw [← hcardK, ← hfact]

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
