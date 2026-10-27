module

public import CFSG.Timmesfeld.Skeleton
public import CFSG.Timmesfeld.ARS.Sec5Sigma

public section

namespace CFSG.Timmesfeld.ARS

@[expose] def CaseLInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    ¬ IsCoatom (Subgroup.normalizer (A : Set G)) → Outcome G

@[expose] def CaseHInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A = lambdaSet R A → Outcome G

@[expose] def CaseBInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      ¬ IsSigmaMaximal R (centralGroup R A) → Outcome G

@[expose] def CaseMaxInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → Outcome G

theorem arsInput_of_cases (hL : CaseLInput) (hH : CaseHInput) (hB : CaseBInput)
    (hM : CaseMaxInput) : ARSInput := by
  intro G _ R h
  obtain ⟨A, hA, -⟩ := h.nondeg
  by_cases hmax : IsCoatom (Subgroup.normalizer (A : Set G))
  · by_cases hSig : sigmaSet R A = lambdaSet R A
    · exact hH G R h A hA hmax hSig
    · by_cases hC : IsSigmaMaximal R (centralGroup R A)
      · exact hM G R h A hA hmax hSig hC
      · exact hB G R h A hA hmax hSig hC
  · exact hL G R h A hA hmax

end CFSG.Timmesfeld.ARS
