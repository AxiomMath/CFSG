module

public import CFSG.Timmesfeld.ARS.Sec9Eight
public import CFSG.Timmesfeld.ARS.Sec9Three

public section

namespace CFSG.Timmesfeld.ARS

open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

theorem levi_cases (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A)
    (h813 : ∀ Δ ∈ leviComps R A A₀, (∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y) → ∀ E ∈ Δ, ∀ E' ∈ Δ,
      (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E')
    (hr : 1 < Nat.card (leviComps R A A₀)) :
    (Nat.card (leviComps R A A₀) = 2 ∧ ∃ Δ₁ ∈ leviComps R A A₀, ∃ Δ₂ ∈ leviComps R A A₀,
      Δ₁ ≠ Δ₂ ∧ ¬ IsSL2Comp Δ₁ ∧ IsSL2Comp Δ₂) ∨
    (Nat.card (leviComps R A A₀) = 3 ∧ ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ) := by
  have hH3 : ∀ Δ₁ ∈ leviComps R A A₀, ¬ IsSL2Comp Δ₁ → OrbitCollinear R A A₀ Δ₁ :=
    fun Δ₁ hΔ₁ hS => orbitCollinear_of_not_isSL2Comp h hA hAne hmax hA₀ hΔ₁ hS (h813 Δ₁ hΔ₁)
  have hH6 : ∀ Blk, IsBlock R A A₀ Blk → OrbitCollinear R A A₀ Blk → ∀ Δ ∈ leviComps R A A₀,
      (∀ Y ∈ Δ, Y ∉ Blk) → CollinearComp R A A₀ Δ := fun Blk hBlk h3 Δ hΔ hout =>
    collinearComp_of_notMem h hA hAne hmax hA₀ hBlk.1 hBlk.2 h3 hΔ hout
  refine levi_cases_of h hA hAne hmax hA₀ hH3 hH6 (fun Blk hBlk h3 Δ₂ hΔ₂ h2out hone => ?_) hr
  have honly : ∀ X ∈ leviSet R A A₀, X ∉ Blk → X ∈ Δ₂ := by
    intro X hX hXB
    have hout : ∀ Y ∈ comp R A A₀ X, Y ∉ Blk := fun Y hY hYB =>
      hXB (hBlk.2 Y hYB (Sec3.reflTransGen_oppGraph_symm hY))
    rw [← hone (comp R A A₀ X) (comp_mem_leviComps hX) hout]
    exact self_mem_comp A A₀ X
  have hdeg : ∀ X ∈ Δ₂, ∀ Y ∈ Δ₂, ¬ Special R X Y := fun X hX Y hY =>
    not_special_of_notMem h hA hAne hmax hA₀ hBlk.1 hBlk.2 h3 hΔ₂ h2out hX hY
  exact isSL2Comp_of_single h hA hAne hA₀ hBlk.1 hBlk.2 h3 hΔ₂ h2out honly
    (hH6 Blk hBlk h3 Δ₂ hΔ₂ h2out) (h813 Δ₂ hΔ₂ hdeg)

theorem levi_cases_or_lieModel {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (h813 : ∀ Δ ∈ leviComps R A A₀, (∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y) → ∀ E ∈ Δ, ∀ E' ∈ Δ,
      (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E')
    (hr : 1 < Nat.card (leviComps R A A₀)) :
    (Nat.card (leviComps R A A₀) = 2 ∧ ∃ Δ₁ ∈ leviComps R A A₀, ∃ Δ₂ ∈ leviComps R A A₀,
      Δ₁ ≠ Δ₂ ∧ ¬ IsSL2Comp Δ₁ ∧ IsSL2Comp Δ₂) ∨
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ Blueprint.LieModel G .POmegaPlus 4 2 f := by
  rcases levi_cases h hA hAne hmax hA₀ h813 hr with h2 | ⟨-, hall⟩
  · exact Or.inl h2
  · exact Or.inr (lieModel_of_forall_isSL2Comp h hA hAne hmax hA₀ hr hall)

end Sec9

end CFSG.Timmesfeld.ARS
