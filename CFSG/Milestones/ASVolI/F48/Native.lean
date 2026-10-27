module

public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Milestones.ASVolI.F4Conjugacy
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open

section


open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots in
theorem burnsideF48_yamPair_two {κ : ChF.GLKind} {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) :
    burnsideF48_YamPair Gp M₁ M₂ := by
  have hyp4 := hyp.toHypF_4_4g
  haveI := hyp4.finite
  haveI := hyp4.normal
  rw [burnsideF48_YamPair, Subgroup.inf_subgroupOf_left M₁ Gp, Subgroup.inf_subgroupOf_left M₂ Gp]
  cases κ
  · exact burnsideF4d_Y1_yam hyp4
  · obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp4
    obtain ⟨T, hT⟩ := burnsideF4g_yamSp4 hf marking
    rw [← h1, ← h2] at hT
    exact ⟨T, hT⟩
  · obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 hyp4
    letI := fK
    haveI := finK
    haveI : CharP K 2 := burnsideF4f_charP_of_card (by omega) hcard
    have hK3 : 3 ≤ Nat.card K := by
      rw [hcard]
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    obtain ⟨T, hT⟩ := burnsideF4g_yamG2 hK3 marking
    rw [← h1, ← h2] at hT
    exact ⟨T, hT⟩
  · obtain ⟨K, fK, finK, sigma, hscope, marking, h1, h2⟩ := burnsideF4g_chart_D4tw hyp4
    letI := fK
    haveI := finK
    obtain ⟨T, hT⟩ := burnsideF4g_yamD4 sigma hscope marking
    rw [← h1, ← h2] at hT
    exact ⟨T, hT⟩
  · obtain ⟨-, hodd, h | h⟩ := hyp.model
    · omega
    · obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, h1, h2⟩ := burnsideF4g_chart_F4tw hyp4
      letI := fK
      haveI := finK
      obtain ⟨T, hT⟩ := burnsideF4g_yamF4 (by omega) hscope marking
      rw [← h1, ← h2] at hT
      exact ⟨T, hT⟩
  · obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp4
    obtain ⟨T, hT⟩ := burnsideF4g_yamU4 marking
    rw [← h1, ← h2] at hT
    exact ⟨T, hT⟩
  · obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp4
    obtain ⟨T, hT⟩ := burnsideF4g_yamU5 marking
    rw [← h1, ← h2] at hT
    exact ⟨T, hT⟩
  · obtain ⟨-, hf1, -⟩ := hyp.model
    omega
  · obtain ⟨-, hf1, -⟩ := hyp.model
    omega

theorem burnsideF48_concl_two_ge4_of_compat (hcompat : ChF.NativeChartCompatibilityGoal)
    {κ : ChF.GLKind} {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) : ChF.F48Concl κ 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_ge4 hf hyp (burnsideF48_parabolics_of_compat hcompat hyp)
    (burnsideF48_yamPair_two hf hyp)

end

section


theorem burnsideF48_concl_two_ge4_native {κ : ChF.GLKind} {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ 2 f Gp M₁ M₂) :
    ChF.F48Concl κ 2 f Gp M₁ M₂ :=
  burnsideF48_concl_two_ge4_of_compat ChF.nativeChartCompatibility hf hyp

end

end CFSG.ASVolI
