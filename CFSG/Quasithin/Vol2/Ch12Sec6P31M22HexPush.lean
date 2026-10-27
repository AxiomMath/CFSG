module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecNS
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.H13.P31Sec.M22Hex

theorem push_mem_map_subtype_iff {Γ : Type} [Group Γ] (X : Subgroup Γ) (B' : Subgroup ↥X)
    (y : ↥X) : (y : Γ) ∈ B'.map X.subtype ↔ y ∈ B' := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    exact hzy' ▸ hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem push_to_gamma {Γ : Type} [Group Γ] (X S₀ : Subgroup Γ) (hS₀X : S₀ ≤ X)
    (B' : Subgroup ↥X) (hSB : S₀.subgroupOf X ≤ B')
    (hNS : AllNS (↥(alternatingGroup (Fin 6))) ↥B')
    (hφ : ∃ φ : ↥B' →* ↥(alternatingGroup (Fin 6)), Function.Surjective φ)
    (hself : ∀ x ∈ Subgroup.normalizer (B' : Set ↥X), x ∈ B')
    (hchar : ∀ α : ↥X ≃* ↥X, (∀ x : ↥X, x ∈ S₀.subgroupOf X ↔ α x ∈ S₀.subgroupOf X) →
      ∀ x : ↥X, x ∈ B' ↔ α x ∈ B') :
    ∃ B : Subgroup Γ, S₀ ≤ B ∧ B ≤ X ∧ AllNS (↥(alternatingGroup (Fin 6))) ↥B ∧
      (∃ φ : ↥B →* ↥(alternatingGroup (Fin 6)), Function.Surjective φ) ∧
      (∀ x ∈ X, x ∈ Subgroup.normalizer (B : Set Γ) → x ∈ B) ∧
      (∀ g ∈ Subgroup.normalizer (X : Set Γ), g ∈ Subgroup.normalizer (S₀ : Set Γ) →
        g ∈ Subgroup.normalizer (B : Set Γ)) := by
  have hBX : B'.map X.subtype ≤ X := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  let e : ↥B' ≃* ↥(B'.map X.subtype) :=
    Subgroup.equivMapOfInjective B' X.subtype X.subtype_injective
  refine ⟨B'.map X.subtype, ?_, hBX, AllNS.of_mulEquiv e hNS, ?_, ?_, ?_⟩
  ·
    intro s hs
    have hsX : s ∈ X := hS₀X hs
    have hmem : (⟨s, hsX⟩ : ↥X) ∈ S₀.subgroupOf X := Subgroup.mem_subgroupOf.2 hs
    exact (push_mem_map_subtype_iff X B' ⟨s, hsX⟩).2 (hSB hmem)
  ·
    obtain ⟨φ, hφs⟩ := hφ
    refine ⟨φ.comp e.symm.toMonoidHom, fun a => ?_⟩
    obtain ⟨b, hb⟩ := hφs a
    exact ⟨e b, by simpa using hb⟩
  ·
    intro x hxX hx
    have hx' : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.normalizer (B' : Set ↥X) := by
      refine Subgroup.mem_set_normalizer_iff.2 (fun h => ?_)
      have h1 := Subgroup.mem_normalizer_iff.1 hx (h : Γ)
      have h2 := push_mem_map_subtype_iff X B' h
      have h4 := push_mem_map_subtype_iff X B'
        ((⟨x, hxX⟩ : ↥X) * h * (⟨x, hxX⟩ : ↥X)⁻¹)
      exact h2.symm.trans (h1.trans h4)
    exact (push_mem_map_subtype_iff X B' ⟨x, hxX⟩).2 (hself _ hx')
  ·
    intro g hgX hgS
    have hconj : ∀ y : ↥X, g * (y : Γ) * g⁻¹ ∈ X := fun y =>
      (Subgroup.mem_normalizer_iff.1 hgX (y : Γ)).1 y.2
    have hconj' : ∀ y : ↥X, g⁻¹ * (y : Γ) * g ∈ X := fun y =>
      (Subgroup.mem_normalizer_iff''.1 hgX (y : Γ)).1 y.2
    let α : ↥X ≃* ↥X :=
      { toFun := fun y => ⟨g * (y : Γ) * g⁻¹, hconj y⟩
        invFun := fun y => ⟨g⁻¹ * (y : Γ) * g, hconj' y⟩
        left_inv := fun y => Subtype.ext (by simp [mul_assoc])
        right_inv := fun y => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
    have hαS : ∀ y : ↥X, y ∈ S₀.subgroupOf X ↔ α y ∈ S₀.subgroupOf X := by
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.1 hgS (y : Γ)
    have hαB := hchar α hαS
    refine Subgroup.mem_normalizer_iff.2 (fun h => ?_)
    by_cases hhX : h ∈ X
    · exact (push_mem_map_subtype_iff X B' (⟨h, hhX⟩ : ↥X)).trans
        ((hαB (⟨h, hhX⟩ : ↥X)).trans
          (push_mem_map_subtype_iff X B' (α (⟨h, hhX⟩ : ↥X))).symm)
    · have hk : g * h * g⁻¹ ∉ X := fun hk => hhX ((Subgroup.mem_normalizer_iff.1 hgX h).2 hk)
      exact ⟨fun hB => absurd (hBX hB) hhX, fun hB => absurd (hBX hB) hk⟩

end CFSG.Quasithin.H13.P31Sec.M22Hex
