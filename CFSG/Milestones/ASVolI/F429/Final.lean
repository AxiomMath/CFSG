module

public import CFSG.Milestones.ASVolI.F429.Corr
public import CFSG.Milestones.ASVolI.F429.Cl47
public import CFSG.Milestones.ASVolI.F429.Cl8

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

@[expose] def burnsideF429_Even2 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, κ.IsLie → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C2 κ f Gp M₁ M₂ hyp T

@[expose] def burnsideF429_Even5 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, κ.IsLie → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C5corr κ Gp M₁ M₂ hyp T

@[expose] def burnsideF429_Even6 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, κ.IsLie → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C6 κ f Gp M₁ M₂ T

section Assembly


theorem burnsideF429_C5corr_of_odd {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C5corr κ Gp M₁ M₂ hyp T := by
  haveI := hyp.finite
  have hTS := burnsideF429_T_eq_of_odd hyp hodd hT
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  left
  rw [hTS, sup_eq_left.2 (burnsideF429_sbar_le_oPPrime (hSB.trans (inf_le_inf_left Gp inf_le_left))),
    sup_eq_left.2 (burnsideF429_sbar_le_oPPrime (hSB.trans (inf_le_inf_left Gp inf_le_right)))]
  exact ⟨rfl, rfl⟩

theorem burnsideF429_corr_of (h2 : burnsideF429_Even2) (h5 : burnsideF429_Even5)
    (h6 : burnsideF429_Even6) : burnsideF429_F_4_29_corr := by
  rw [burnsideF429_corr_iff]
  intro κ f E _ Gp M₁ M₂ hyp hκ T hT
  have h256 : burnsideF429_C2 κ f Gp M₁ M₂ hyp T ∧ burnsideF429_C5corr κ Gp M₁ M₂ hyp T ∧
      burnsideF429_C6 κ f Gp M₁ M₂ T := by
    by_cases hodd : Odd Gp.index
    · exact ⟨burnsideF429_C2_of_odd hyp hodd hT, burnsideF429_C5corr_of_odd hyp hodd hT,
        burnsideF429_C6_of_odd hyp hodd hT⟩
    · exact ⟨h2 κ f E Gp M₁ M₂ hyp hκ hodd T hT, h5 κ f E Gp M₁ M₂ hyp hκ hodd T hT,
        h6 κ f E Gp M₁ M₂ hyp hκ hodd T hT⟩
  exact ⟨burnsideF429_clause1 κ f E Gp M₁ M₂ hyp hκ, h256.1,
    burnsideF429_clause3 κ f E Gp M₁ M₂ hyp hκ, burnsideF429_clause4 κ f E Gp M₁ M₂ hyp hκ,
    h256.2.1, h256.2.2, burnsideF429_clause7 κ f E Gp M₁ M₂ hyp hκ T hT,
    burnsideF429_clause8 κ f E Gp M₁ M₂ hyp hκ⟩

end Assembly

end CFSG.ASVolI
