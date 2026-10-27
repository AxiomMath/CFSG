module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem irrOn_of_zpowers_transitive {A U : Subgroup G} {y : G} (hyA : y ∈ A)
    (htr : ∀ u ∈ U, ∀ w ∈ U, u ≠ 1 → w ≠ 1 → ∃ k : ℤ, y ^ k * u * (y ^ k)⁻¹ = w) :
    IrrOn A U := by
  intro W hWU hAW
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := W)).mp hW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwU : w ∈ U := hWU hwW
  have hyN : y ∈ normalizer (W : Set G) := hAW hyA
  have hUW : U ≤ W := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]; exact W.one_mem
    · obtain ⟨k, hk⟩ := htr u hu w hwU hu1 hw1'
      have hu_eq : u = (y ^ k)⁻¹ * w * y ^ k := by
        have h := congrArg (fun z => (y ^ k)⁻¹ * z * y ^ k) hk
        rw [← h]; group
      have hmem : (y ^ k)⁻¹ * w * y ^ k ∈ W := by
        have hyk : y ^ k ∈ normalizer (W : Set G) := Subgroup.zpow_mem _ hyN k
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyk) w).mp hwW
        simpa using h
      rw [hu_eq]
      exact hmem
  exact le_antisymm hWU hUW

theorem commutator_iSup_le_centralizer {ι : Sort*} {V X : Subgroup G} {A : ι → Subgroup G}
    (hA : ∀ i, A i ≤ normalizer (V : Set G))
    (h : ∀ i, ⁅A i, X⁆ ≤ centralizer (V : Set G)) :
    ⁅⨆ i, A i, X⁆ ≤ centralizer (V : Set G) := by
  have key : ∀ a ∈ ⨆ i, A i, ∀ y ∈ X, ⁅a, y⁆ ∈ centralizer (V : Set G) := by
    have hconj : ∀ {x c : G}, x ∈ normalizer (V : Set G) →
        c ∈ centralizer (V : Set G) → x * c * x⁻¹ ∈ centralizer (V : Set G) := by
      intro x c hx hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro v hv
      have hv' : x⁻¹ * v * x ∈ V := (Subgroup.mem_normalizer_iff''.mp hx v).mp hv
      calc
        v * (x * c * x⁻¹) = x * ((x⁻¹ * v * x) * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * v * x)) * x⁻¹ := by rw [hc _ hv']
        _ = x * c * x⁻¹ * v := by group
    let H : Subgroup G :=
      { carrier := {x | x ∈ normalizer (V : Set G) ∧
          ∀ y ∈ X, ⁅x, y⁆ ∈ centralizer (V : Set G)}
        one_mem' := by
          refine ⟨Subgroup.one_mem _, ?_⟩
          intro y hy
          rw [commutatorElement_def]
          simp
        mul_mem' := by
          rintro x₁ x₂ ⟨hx₁, hc₁⟩ ⟨hx₂, hc₂⟩
          refine ⟨Subgroup.mul_mem _ hx₁ hx₂, ?_⟩
          intro y hy
          rw [commutatorElement_mul_left_eq_conj_mul]
          exact Subgroup.mul_mem _ (hconj hx₁ (hc₂ y hy)) (hc₁ y hy)
        inv_mem' := by
          rintro x ⟨hx, hc⟩
          refine ⟨Subgroup.inv_mem _ hx, ?_⟩
          intro y hy
          rw [commutatorElement_inv_left, ← commutatorElement_inv]
          simpa using hconj (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ (hc y hy)) }
    have hle : ⨆ i, A i ≤ H := by
      refine iSup_le fun i => ?_
      intro a ha
      exact ⟨hA i ha, fun y hy => h i (Subgroup.commutator_mem_commutator ha hy)⟩
    intro a ha y hy
    exact (hle ha).2 y hy
  rw [Subgroup.commutator_le]
  exact key

end CFSG.LocalAnalysis.UniquenessCase.UC22
