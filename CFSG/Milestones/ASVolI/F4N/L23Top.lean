module

public import CFSG.Milestones.ASVolI.F4N.L23c
public import CFSG.Milestones.ASVolI.F4SmallCompletions
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.G2d
public import CFSG.Milestones.ASVolI.F48.Small.Tits
public import CFSG.Milestones.ASVolI.F4N.L11

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section F423s

set_option linter.unusedSectionVars false

theorem burnsideF423s_five {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hGp : Gp = ⊤) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  have hF := burnsideF4n_facts46All as_F_4_6
  have hι := burnsideF4b_IotaSmall_of hF as_F_4_5
  have h48c : F48Concl κ p f Gp M₁ M₂ := by
    rcases hκ with rfl | rfl
    · exact burnsideF48s_small_G2d as_F_4_5 as_F_4_6 hyp
    · exact burnsideF48s_small_Tits as_F_4_5 as_F_4_6 hyp
  obtain ⟨⟨Y₀, _, β₀, -, -, hall⟩, -⟩ := h48c.2 hGp
  exact burnsideF4n_isQuasiEquivalent_trans (hall Y β hβ hs)
    (burnsideF4n_isQuasiEquivalent_symm
      (hall _ (incl M₁ M₂) (incl_faithful M₁ M₂) (hι κ p f E Gp M₁ M₂ hyp)))

theorem burnsideF423s_F_4_23 : F_4_23 := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ
  refine ⟨burnsideF4n_F423_four as_F_4_5 as_F_4_6 as_F_4_20 hyp hGp hκ,
    fun Y _ β hβ hs cc hcc hccl y hy hyx y' hy' hy'x Y' _ ρ hρ => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ⟨fun hsρ => burnsideF4n_phat_of_small as_F_4_6 as_F_4_20 hyp hGp hκ β hβ hcc hccl hy hyx
      hy' hy'x ρ hρ hsρ, fun hne => burnsideF4n_small_of_phat as_F_4_6 hyp hκ β hβ hccl ρ hρ hne⟩
  · exact burnsideF4n_F423_two as_F_4_5 as_F_4_6 hyp hκ β hβ hccl ρ hρ
  · rintro ⟨st, h1, h2⟩
    exact (burnsideF4n_F423_two as_F_4_5 as_F_4_6 hyp hκ β hβ hccl ρ hρ st h1 h2).2.2
  · intro F _ j F₁ F₂ _ _ ι hι
    subst hι
    exact burnsideF423s_five hyp hGp hκ β hβ hs

end F423s

end CFSG.ASVolI
