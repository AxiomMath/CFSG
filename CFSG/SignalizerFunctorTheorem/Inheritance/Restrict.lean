module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic
public import CFSG.SignalizerFunctorTheorem.Inheritance.Pullback
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.SignalizerFunctorTheorem

theorem noFaithfulSection_subgroupOf {G : Type*} [Group G] {A W B : Subgroup G} (hAB : A ≤ B)
    (h : NoFaithfulSection A W) :
    NoFaithfulSection (A.subgroupOf B) (W.subgroupOf B) := by
  intro K₁ L₁ hK₁ hL₁ hnorm hAK hAL hsimple hnonab
  have hι : Function.Injective B.subtype := B.subtype_injective
  have hnormalizer : ∀ {K₂ : Subgroup B}, A.subgroupOf B ≤ Subgroup.normalizer (K₂ : Set B) →
      A ≤ Subgroup.normalizer ((K₂.map B.subtype : Subgroup G) : Set G) := by
    intro K₂ hK a ha
    have h1 := Subgroup.mem_normalizer_iff.mp
      (hK (show (⟨a, hAB ha⟩ : B) ∈ A.subgroupOf B from ha))
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨a, hAB ha⟩ * k * ⟨a, hAB ha⟩⁻¹, (h1 k).mp hk, rfl⟩
    · rintro ⟨k, hk, hkg⟩
      refine ⟨⟨a, hAB ha⟩⁻¹ * k * ⟨a, hAB ha⟩, ?_, ?_⟩
      · refine (h1 (⟨a, hAB ha⟩⁻¹ * k * ⟨a, hAB ha⟩)).mpr ?_
        have h2 : (⟨a, hAB ha⟩ : B) * (⟨a, hAB ha⟩⁻¹ * k * ⟨a, hAB ha⟩) * ⟨a, hAB ha⟩⁻¹ = k := by
          group
        rw [h2]
        exact hk
      · have h3 : (k : G) = a * g * a⁻¹ := hkg
        change a⁻¹ * (k : G) * a = g
        rw [h3]
        group
  have := normal_map_subgroupOf B.subtype hL₁
  let e := mapSectionEquiv (K := K₁) (L := L₁) hι
  have := hsimple
  obtain ⟨a, haA, ha1, hmem⟩ := h (K₁.map B.subtype) (L₁.map B.subtype)
    (by
      rintro g ⟨k, hk, rfl⟩
      exact hK₁ hk)
    (Subgroup.map_mono hL₁) (hnormalizer hAK) (hnormalizer hAL) e.symm.isSimpleGroup
    (by
      obtain ⟨x, y, hxy⟩ := hnonab
      exact ⟨e x, e y, fun hc => hxy (by simpa using congrArg e.symm hc)⟩)
  refine ⟨⟨a, hAB haA⟩, haA, fun h1 => ha1 (congrArg Subtype.val h1), fun x hx => ?_⟩
  obtain ⟨l, hl, hlx⟩ := hmem x (Subgroup.mem_map_of_mem B.subtype hx)
  have : l = x⁻¹ * (⟨a, hAB haA⟩ * x * ⟨a, hAB haA⟩⁻¹) := Subtype.ext hlx
  rw [← this]
  exact hl

end CFSG.SignalizerFunctorTheorem
