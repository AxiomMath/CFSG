module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l04fHL1A_iso_A5 {o : LargeEvenLabel} {f : ℕ}
    (h : GGLabelIso o (⟨.A, 5, f⟩ : LargeEvenLabel)) : o = ⟨.A, 5, f⟩ := by
  rcases h with h | ⟨-, hBC, -, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ |
    ⟨h2, -⟩
  · exact h
  · rcases hBC with hB | hB <;> cases hB
  all_goals cases h2

private theorem l04fHL1A_iso_twA5 {o : LargeEvenLabel} {f : ℕ}
    (h : GGLabelIso o (⟨.twA, 5, f⟩ : LargeEvenLabel)) : o = ⟨.twA, 5, f⟩ := by
  rcases h with h | ⟨-, hBC, -, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ |
    ⟨h2, -⟩
  · exact h
  · rcases hBC with hB | hB <;> cases hB
  all_goals cases h2

private theorem l04fHL1A_iso_twD4 {o : LargeEvenLabel} {f : ℕ}
    (h : GGLabelIso o (⟨.twD, 4, f⟩ : LargeEvenLabel)) : o = ⟨.twD, 4, f⟩ := by
  rcases h with h | ⟨-, hBC, -, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ |
    ⟨h2, -⟩
  · exact h
  · rcases hBC with hB | hB <;> cases hB
  all_goals cases h2

theorem ggPumpTwJLab_rigid
    {f : ℕ} {Y : Type} [Group Y] (hJ : GGPumpTwJLab f Y) {o : LargeEvenLabel}
    (ho : LargeEvenInLambda2 o) (hY : GGHasLabel o Y) :
    (o = ⟨.A, 5, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨ (o = ⟨.twA, 5, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨ o = ⟨.twD, 4, f⟩ := by
  rcases hJ with ⟨hdiv, htwA⟩ | ⟨hdiv, hA⟩ | htwD
  ·
    have hf : 1 ≤ f := by
      dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
        LargeEvenRecipeUnitary] at htwA
      obtain ⟨K, _, _, hK, -⟩ := htwA
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · rw [h0, pow_zero] at h1
        norm_num at h1
      · exact h0
    have hl₀ : LargeEvenInLambda2 (⟨.twA, 5, f⟩ : LargeEvenLabel) := by
      refine ⟨hf, by norm_num, ?_⟩
      intro h
      norm_num at h
    exact Or.inr (Or.inl
      ⟨l04fHL1A_iso_twA5 (ggLabelRigidInput_holds o _ Y ho hl₀ hY htwA), hdiv⟩)
  ·
    have hf : 1 ≤ f := by
      dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
        LargeEvenRecipeLinear] at hA
      obtain ⟨K, _, _, hK, -⟩ := hA
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · rw [h0, pow_zero] at h1
        norm_num at h1
      · exact h0
    have hl₀ : LargeEvenInLambda2 (⟨.A, 5, f⟩ : LargeEvenLabel) := by
      refine ⟨hf, by norm_num, ?_⟩
      intro h
      norm_num at h
    exact Or.inl
      ⟨l04fHL1A_iso_A5 (ggLabelRigidInput_holds o _ Y ho hl₀ hY hA), hdiv⟩
  ·
    have hf : 1 ≤ f := by
      simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
        LargeEvenRecipeOmegaMinus] at htwD
      obtain ⟨K, _, _, hK, -⟩ := htwD
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · rw [h0, pow_zero] at h1
        norm_num at h1
      · exact h0
    have hl₀ : LargeEvenInLambda2 (⟨.twD, 4, f⟩ : LargeEvenLabel) := ⟨hf, by norm_num⟩
    exact Or.inr (Or.inr
      (l04fHL1A_iso_twD4 (ggLabelRigidInput_holds o _ Y ho hl₀ hY htwD)))

end CFSG.StandardType

end
