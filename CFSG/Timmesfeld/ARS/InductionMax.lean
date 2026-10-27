module

public import CFSG.Timmesfeld.ARS.Induction
public import CFSG.Timmesfeld.ARS.Sec9Main

public section

namespace CFSG.Timmesfeld.ARS

open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem leviSet_nonempty (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) :
    (leviSet R A A₀).Nonempty := by
  obtain ⟨F, hF⟩ := CaseD4.lambdaStar_nonempty h hA hA₀
  obtain ⟨X, hX, -⟩ := exists_mem_leviSet_not_commuting h hA hAne hA₀ hF
  exact ⟨X, hX⟩

theorem finite_leviComps [Finite G] (A A₀ : Subgroup G) : Finite (leviComps R A A₀) :=
  Subtype.finite

theorem card_leviComps_pos (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) :
    0 < Nat.card (leviComps R A A₀) := by
  have := h.finite
  have := finite_leviComps (R := R) A A₀
  obtain ⟨X, hX⟩ := leviSet_nonempty h hA hAne hA₀
  exact Nat.card_pos_iff.2 ⟨⟨_, Sec9.comp_mem_leviComps hX⟩, inferInstance⟩

theorem comp_eq_leviSet_of_card_eq_one (h : Hyp G R) {A A₀ E : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (h1 : Nat.card (leviComps R A A₀) = 1) (hE : E ∈ leviSet R A A₀) :
    comp R A A₀ E = leviSet R A A₀ := by
  have := h.finite
  have := finite_leviComps (R := R) A A₀
  refine Set.Subset.antisymm (comp_subset h hA hAne hA₀ hE) fun Y hY => ?_
  have hsub : Subsingleton (leviComps R A A₀) := (Nat.card_eq_one_iff_unique.1 h1).1
  have e : (⟨_, Sec9.comp_mem_leviComps hY⟩ : leviComps R A A₀) =
      ⟨_, Sec9.comp_mem_leviComps hE⟩ := Subsingleton.elim _ _
  have e' : comp R A A₀ Y = comp R A A₀ E := congrArg Subtype.val e
  rw [← e']
  exact Sec9.self_mem_comp A A₀ Y

@[expose] def Degenerate813Input : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A, ∀ Δ ∈ leviComps R A A₀,
        (∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y) → ∀ E ∈ Δ, ∀ E' ∈ Δ,
          (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E'

@[expose] def CaseOAStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
        Nat.card (leviComps R A A₀) = 2 → ∀ Δ₁ ∈ leviComps R A A₀, ∀ Δ₂ ∈ leviComps R A A₀,
          Δ₁ ≠ Δ₂ → ¬ IsSL2Comp Δ₁ → IsSL2Comp Δ₂ → Output G R

@[expose] def CaseMStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
        Nat.card (leviComps R A A₀) = 1 →
          (∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, ¬ Special R X Y) → Output G R

@[expose] def CaseEStep : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
        Nat.card (leviComps R A A₀) = 1 →
          (∃ X ∈ leviSet R A A₀, ∃ Y ∈ leviSet R A A₀, Special R X Y) → Output G R

theorem caseMaxStep_of_inputs (h813 : Degenerate813Input) (hOA : CaseOAStep) (hM : CaseMStep)
    (hE : CaseEStep) : CaseMaxStep := by
  intro G _ R h IH A hA hcoat hAne hmax
  have := h.finite
  obtain ⟨A₀, hA₀R, hAA₀⟩ := h.noIsolated A hA
  have hA₀ : A₀ ∈ omegaSet R A := ⟨hA₀R, hAA₀⟩
  have hpos := card_leviComps_pos h hA hAne hA₀
  rcases Nat.lt_or_ge 1 (Nat.card (leviComps R A A₀)) with hr | hr
  · rcases Sec9.levi_cases h hA hAne hmax hA₀ (h813 G R h A hA hcoat hAne hmax A₀ hA₀) hr with
      ⟨h2, Δ₁, hΔ₁, Δ₂, hΔ₂, hne, hS₁, hS₂⟩ | ⟨h3, hall⟩
    · exact hOA G R h IH A hA hcoat hAne hmax A₀ hA₀ h2 Δ₁ hΔ₁ Δ₂ hΔ₂ hne hS₁ hS₂
    · obtain ⟨P, Q, hPQ⟩ := Sec9.exists_leviSL2Cube h hA hAne hA₀ h3 hall
      exact .inr (.inl ⟨4, le_rfl, CaseD4.hasGenConfig h hA hAne hmax hA₀ hPQ⟩)
  · have h1 : Nat.card (leviComps R A A₀) = 1 := by omega
    by_cases hnd : ∃ X ∈ leviSet R A A₀, ∃ Y ∈ leviSet R A A₀, Special R X Y
    · exact hE G R h IH A hA hcoat hAne hmax A₀ hA₀ h1 hnd
    · push Not at hnd
      exact hM G R h IH A hA hcoat hAne hmax A₀ hA₀ h1 hnd

end CFSG.Timmesfeld.ARS
