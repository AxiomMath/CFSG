module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.L827X

open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_chief_factor_comm [Finite G] {Λ R U Y₁ : Subgroup G}
    (hΛR : Λ ≤ Subgroup.normalizer (R : Set G)) (hΛU : Λ ≤ Subgroup.normalizer (U : Set G))
    (hUR : U ≤ R) (hYΛ : Y₁ ≤ Λ) (hUY : ⁅U, Y₁⁆ ≤ U) (hRY : ¬ ⁅R, Y₁⁆ ≤ U)
    (hcop : ∀ A : Subgroup G, A ≤ R → Y₁ ≤ Subgroup.normalizer (A : Set G) →
      ⁅⁅A, Y₁⁆, Y₁⁆ = ⁅A, Y₁⁆) :
    ∃ W₀ W₁ : Subgroup G, U ≤ W₀ ∧ W₀ < W₁ ∧ W₁ ≤ R ∧
      Λ ≤ Subgroup.normalizer (W₀ : Set G) ∧ Λ ≤ Subgroup.normalizer (W₁ : Set G) ∧
      (∀ B : Subgroup G, W₀ ≤ B → B ≤ W₁ → Λ ≤ Subgroup.normalizer (B : Set G) →
        B = W₀ ∨ B = W₁) ∧
      ¬ ⁅W₁, Y₁⁆ ≤ W₀ := by
  classical
  obtain ⟨W₁, hW₁⟩ := exists_minimal_of_wellFoundedLT
    (fun A : Subgroup G => A ≤ R ∧ U ≤ A ∧ Λ ≤ Subgroup.normalizer (A : Set G) ∧
      ¬ ⁅A, Y₁⁆ ≤ U) ⟨R, le_rfl, hUR, hΛR, hRY⟩
  obtain ⟨hW₁R, hUW₁, hΛW₁, hW₁Y⟩ := hW₁.1
  have hUlt : U < W₁ := by
    refine lt_of_le_of_ne hUW₁ ?_
    rintro rfl
    exact hW₁Y hUY
  obtain ⟨W₀, hUW₀, hW₀max⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun B : Subgroup G => U ≤ B ∧ B < W₁ ∧ Λ ≤ Subgroup.normalizer (B : Set G)) U
    ⟨le_rfl, hUlt, hΛU⟩
  obtain ⟨⟨hUW₀', hW₀W₁, hΛW₀⟩, hW₀mx⟩ := hW₀max
  refine ⟨W₀, W₁, hUW₀', hW₀W₁, hW₁R, hΛW₀, hΛW₁, ?_, ?_⟩
  ·
    intro B hW₀B hBW₁ hΛB
    by_cases hBeq : B = W₁
    · exact Or.inr hBeq
    · left
      have hlt : B < W₁ := lt_of_le_of_ne hBW₁ hBeq
      have hBle : B ≤ W₀ := hW₀mx ⟨hUW₀'.trans hW₀B, hlt, hΛB⟩ hW₀B
      exact le_antisymm hBle hW₀B
  ·
    intro hW₁W₀
    have hW₀notS : ¬ (W₀ ≤ R ∧ U ≤ W₀ ∧ Λ ≤ Subgroup.normalizer (W₀ : Set G) ∧
        ¬ ⁅W₀, Y₁⁆ ≤ U) := by
      intro hS
      have hle : W₁ ≤ W₀ := hW₁.2 hS hW₀W₁.le
      exact lt_irrefl _ (lt_of_lt_of_le hW₀W₁ hle)
    have hW₀Y : ⁅W₀, Y₁⁆ ≤ U := by
      by_contra hc
      exact hW₀notS ⟨(hW₀W₁.le.trans hW₁R), hUW₀', hΛW₀, hc⟩
    have hY₁N : Y₁ ≤ Subgroup.normalizer (W₁ : Set G) := fun y hy => hΛW₁ (hYΛ hy)
    have hcomm : ⁅⁅W₁, Y₁⁆, Y₁⁆ ≤ U :=
      (Subgroup.commutator_mono hW₁W₀ le_rfl).trans hW₀Y
    apply hW₁Y
    calc ⁅W₁, Y₁⁆ = ⁅⁅W₁, Y₁⁆, Y₁⁆ := (hcop W₁ hW₁R hY₁N).symm
      _ ≤ U := hcomm

end CFSG.Quasithin.H13.L827X
