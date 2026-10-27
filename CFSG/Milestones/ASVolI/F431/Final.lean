module

public import CFSG.Milestones.ASVolI.F431.Odd
public import CFSG.Milestones.ASVolI.F431.BUc5Full
public import CFSG.Milestones.ASVolI.F431.BUc4
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Final

set_option linter.unusedSectionVars false


variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_ctr_le_U4_all (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_mem_of_odd hodd hTb hx.1
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU4 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U4 hyp.model
  obtain ⟨T, N, z, hT, hT1, hT2, hcen⟩ := Un.burnsideF4m_unCenterProp_four_all f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF4m_not_odd hyp hTD hodd)
  exact burnsideF4m_ctr_le_of_lieExt hyp hTD hT hT1 hT2 hcen hTb hx

theorem burnsideF4m_ctr_le_U5_all (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂)
    {Tb : Subgroup E} (hTb : IsSylowTwoOf Tb (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr Tb) : x ∈ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_mem_of_odd hodd hTb hx.1
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU5 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U5 hyp.model
  obtain ⟨T, N, z, hT, hT1, hT2, hcen⟩ := Un.burnsideF4m_unCenterProp_five_all f ↥Gp hmodel
    (burnsideF4d_lieExtE hyp.toHypF_4_4g hTD).toLieAmalgamExt (burnsideF4m_not_odd hyp hTD hodd)
  exact burnsideF4m_ctr_le_of_lieExt hyp hTD hT hT1 hT2 hcen hTb hx

theorem burnsideF4m_ctrInputUn : burnsideF4m_CtrInputUn := by
  intro κ f E _ Gp M₁ M₂ hyp hκ T hT x hx _
  rcases hκ with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact burnsideF4m_ctr_le_U4_all hyp hT hx
  · exact burnsideF4m_ctr_le_U5_all hyp hT hx

theorem burnsideF4m_F_4_33 : F_4_33 :=
  burnsideF4m_F_4_33_of_un burnsideF4m_ctrInputUn

variable {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_odd_index_U5_lie' (hlie : burnsideF4m_LieCoreInput)
    (hyp : HypF_4_31 .U5 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2, hQ2⟩ := hlie.2.1 _ f E Gp M₁ M₂ hyp.amalgam hf (Or.inr rfl) hodd
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU5 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U5 hyp.amalgam.model
  exact burnsideF4m_false_of_unOut hyp hf (Or.inr rfl) hZ1 hZ2 hQ2 hTD
    (Un.burnsideF4m_f431UnOutLieProp_five f hf ↥Gp hmodel _
      (burnsideF4m_not_odd hyp.amalgam hTD hodd))

@[expose] def burnsideF4m_OddIndexSmall' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ((κ = .Sp4 ∧ f = 1) ∨ (κ = .U4 ∧ f = 1) ∨ (κ = .U5 ∧ f = 1)) → Odd Gp.index

theorem burnsideF4m_oddIndexSmall_of (hlie : burnsideF4m_LieCoreInput)
    (hsmall : burnsideF4m_OddIndexSmall') : burnsideF4m_OddIndexSmall := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ
  rcases hκ with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · exact hsmall _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inl ⟨rfl, hf⟩)
  · exact hsmall _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inl ⟨rfl, hf⟩))
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_odd_index_U5_lie' hlie hyp hf2
    · exact hsmall _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inr ⟨rfl, by omega⟩))

theorem burnsideF4m_F_4_38_of_lie' (hlie : burnsideF4m_LieCoreInput)
    (hsmall : burnsideF4m_OddIndexSmall') : F_4_38 :=
  burnsideF4m_F_4_38_of_lie hlie (burnsideF4m_oddIndexSmall_of hlie hsmall)

end Final

end CFSG.ASVolI
