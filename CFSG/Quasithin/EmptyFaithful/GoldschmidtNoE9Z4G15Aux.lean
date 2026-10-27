module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.NoE9Z4GenGrp

variable {G : Type*} [Group G]

theorem index_two_cosets [Finite G] {U U0 W : Subgroup G} (hW : W ≤ U0)
    (hWU : W.relIndex U ≤ 2) {u₁ : G} (hu₁ : u₁ ∈ U) (hu₁0 : u₁ ∉ U0) :
    ∀ u ∈ U, ∀ u' ∈ U, u ∉ U0 → u' ∉ U0 → u⁻¹ * u' ∈ U0 := by
  have hdvd : U0.relIndex U ∣ W.relIndex U := Subgroup.relIndex_dvd_of_le_left U hW
  have hne : W.relIndex U ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_dvd_card (H := W) (K := U)
    rw [h0] at h1
    exact (Nat.card_pos (α := ↥U)).ne' (Nat.eq_zero_of_zero_dvd h1)
  have hle : U0.relIndex U ≤ 2 := (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hWU
  have hne1 : U0.relIndex U ≠ 1 := fun h1 => hu₁0 (Subgroup.relIndex_eq_one.mp h1 hu₁)
  have hne0 : U0.relIndex U ≠ 0 := fun h0 => hne (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have h2 : (U0.subgroupOf U).index = 2 := by
    have : U0.relIndex U = 2 := by omega
    exact this
  intro u hu u' hu' hn hn'
  have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨u, hu⟩ : ↥U)⁻¹) (b := ⟨u', hu'⟩)).mpr
    (by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact absurd (by simpa using U0.inv_mem (Subgroup.mem_subgroupOf.mp h)) hn
      · exact absurd (Subgroup.mem_subgroupOf.mp h) hn')
  exact Subgroup.mem_subgroupOf.mp h3

theorem exists_hom_of_index_two {U U0 Z : Subgroup G} {z : G} (hz : z ∈ Z) (hz2 : z * z = 1)
    (hidx : ∀ u ∈ U, ∀ u' ∈ U, u ∉ U0 → u' ∉ U0 → u⁻¹ * u' ∈ U0) :
    ∃ f : ↥U →* ↥Z, (∀ u : ↥U, (u : G) ∈ U0 → f u = 1) ∧
      ∀ u : ↥U, (u : G) ∉ U0 → (f u : G) = z := by
  classical
  let fa : ↥U → ↥Z := fun u => if (u : G) ∈ U0 then 1 else ⟨z, hz⟩
  have fa_pos : ∀ u : ↥U, (u : G) ∈ U0 → fa u = 1 := fun u h => by simp [fa, h]
  have fa_neg : ∀ u : ↥U, (u : G) ∉ U0 → fa u = ⟨z, hz⟩ := fun u h => by simp [fa, h]
  have hmul : ∀ a b : ↥U, fa (a * b) = fa a * fa b := by
    intro a b
    have hab' : ((a * b : ↥U) : G) = (a : G) * (b : G) := rfl
    by_cases ha : (a : G) ∈ U0 <;> by_cases hb : (b : G) ∈ U0
    · rw [fa_pos a ha, fa_pos b hb, fa_pos (a * b) (by rw [hab']; exact U0.mul_mem ha hb), one_mul]
    · have hab : ((a * b : ↥U) : G) ∉ U0 := fun h => hb (by
        rw [hab'] at h
        have := U0.mul_mem (U0.inv_mem ha) h
        simpa using this)
      rw [fa_pos a ha, fa_neg b hb, fa_neg (a * b) hab, one_mul]
    · have hab : ((a * b : ↥U) : G) ∉ U0 := fun h => ha (by
        rw [hab'] at h
        have := U0.mul_mem h (U0.inv_mem hb)
        simpa using this)
      rw [fa_neg a ha, fa_pos b hb, fa_neg (a * b) hab, mul_one]
    · have hab : ((a * b : ↥U) : G) ∈ U0 := by
        rw [hab']
        have := hidx (a : G)⁻¹ (U.inv_mem a.2) (b : G) b.2
          (fun h => ha (by simpa using U0.inv_mem h)) hb
        simpa using this
      rw [fa_neg a ha, fa_neg b hb, fa_pos (a * b) hab]
      exact (Subtype.ext hz2).symm
  refine ⟨MonoidHom.mk' fa hmul, fun u hu => fa_pos u hu, fun u hu => ?_⟩
  show ((fa u : ↥Z) : G) = z
  rw [fa_neg u hu]

end CFSG.Quasithin.NoE9Z4GenGrp
