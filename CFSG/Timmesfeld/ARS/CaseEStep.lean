module

public import CFSG.Timmesfeld.ARS.InductionMax
public import CFSG.Timmesfeld.ARS.Sec13Basic

public section

namespace CFSG.Timmesfeld.ARS

theorem Sec13.of_caseE {G : Type*} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A : Subgroup G} (hA : A ∈ R) (hcoat : IsCoatom (Subgroup.normalizer (A : Set G)))
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ omegaSet R A) (h1 : Nat.card (leviComps R A A₀) = 1)
    (hnd : ∃ X ∈ leviSet R A A₀, ∃ Y ∈ leviSet R A A₀, Special R X Y) : Sec13 R A A₀ where
  hyp := h
  mem := hA
  sec8 := ⟨hcoat, hAne⟩
  max := hmax
  opp := hA₀
  conn E hE F hF := by
    have hF' : F ∈ Levi.comp R A A₀ E := by
      rw [comp_eq_leviSet_of_card_eq_one h hA hAne hA₀ h1 hE]
      exact hF
    exact hF'
  nondeg := hnd

@[expose] def CaseENonSimplyLacedInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → IndHyp G → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
        Nat.card (leviComps R A A₀) = 1 →
          (∃ X ∈ leviSet R A A₀, ∃ Y ∈ leviSet R A A₀, Special R X Y) →
            ¬ (NonSimplyLacedOutcome (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀)) ∧
              NSLData (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀))
                (quotClass (levi R A A₀) (leviSet R A A₀)))

end CFSG.Timmesfeld.ARS
