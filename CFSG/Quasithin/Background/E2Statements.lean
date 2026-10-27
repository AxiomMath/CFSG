module

public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

@[expose] def E213TwoConcl {Γ : Type} [Group Γ] (H T V : Subgroup Γ) : Prop :=
  ∃ g ∈ H, ∃ A : Subgroup Γ, A ≤ T ∧ A ≤ cjSub g V ∧ IsElemAbelian 2 A ∧
    ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧ ¬ A ≤ Subgroup.centralizer (V : Set Γ) ∧
    A ⊓ Subgroup.centralizer (V : Set Γ) = V ⊓ cjSub g V ∧
    (V ⊓ Subgroup.centralizer (A : Set Γ)).relIndex V ≤
      ((A ⊓ Subgroup.centralizer (V : Set Γ)).relIndex A) ^ 2

@[expose] def E213TwoStatement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ), Hyp28 H T M V → CharTwo H →
    E213TwoConcl H T V

@[expose] def E213TwoNonsolvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ), Hyp28 H T M V → CharTwo H →
    ¬ Group.IsSolvable H → E213TwoConcl H T V

@[expose] def E213ThreeStatement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
    qhatOf (autI h.elem H) ≤ ((2 : ℚ) : WithTop ℚ)

@[expose] def E213ThreeNonsolvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
    ¬ Group.IsSolvable H → qhatOf (autI h.elem H) ≤ ((2 : ℚ) : WithTop ℚ)

@[expose] def E215Nonsolvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
    IsTISetIn V M → ¬ Group.IsSolvable H → qhatOf (autI h.elem H) < ((2 : ℚ) : WithTop ℚ)

theorem e213TwoStatement_of_nonsolvable (hns : E213TwoNonsolvable) : E213TwoStatement := by
  intro Γ _ _ H T M V h hchar
  by_cases hsolv : Group.IsSolvable H
  · exact h.e2_13_two hsolv hchar
  · exact hns Γ H T M V h hchar hsolv

theorem e213ThreeStatement_of_nonsolvable (hns : E213ThreeNonsolvable) :
    E213ThreeStatement := by
  intro Γ _ _ H T M V h hchar
  by_cases hsolv : Group.IsSolvable H
  · exact h.e2_13_three hsolv hchar
  · exact hns Γ H T M V h hchar hsolv

theorem e215Statement_of_nonsolvable (hns : E215Nonsolvable) :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
      IsTISetIn V M → qhatOf (autI h.elem H) < ((2 : ℚ) : WithTop ℚ) := by
  intro Γ _ _ H T M V h hchar hTI
  by_cases hsolv : Group.IsSolvable H
  · exact h.e2_15 hsolv hchar
  · exact hns Γ H T M V h hchar hTI hsolv

theorem e213ThreeStatement_of_two (h2 : E213TwoStatement) : E213ThreeStatement := by
  intro Γ _ _ H T M V h hchar
  obtain ⟨-, -, A, hAT, -, hAel, hcub, hAV, -, hcount⟩ := h2 Γ H T M V h hchar
  exact qhatOf_le_two_of_cubic (hAT.trans h.minParabolic.isSylow.1) (hAT.trans h.normal_T) hAel
    hcub hAV hcount

end E2

end CFSG.Quasithin
