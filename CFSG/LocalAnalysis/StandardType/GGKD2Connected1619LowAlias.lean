module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

theorem noSetupAt_twA_of_leaves (hSplit : corner1584_split_lift)
    (hNon : corner1584_nonsplit_shape) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) (hne : lab ≠ (⟨.twA, 5, 1⟩ : LargeEvenLabel)) :
    LargeEvenLabelAll lab (fun R _ I _ => NoSetupAt R I) := by
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_)
    (largeEvenLabelAll_and (hSplit lab hlab) (hNon lab hlab))
  obtain ⟨hs, hn⟩ := h
  intro L' _ _ ψ hψ hker hperf e J a hset
  have hcl : ClassicalLab lab := Or.inr htag
  by_cases hsp : SplitLift lab R I ψ e
  · exact hs L' ψ hψ hker hperf e J a hset hcl hsp
  · exact hne (hn L' ψ hψ hker hperf e J a hset hcl hsp).1

theorem noSetupTwD3_of_leaves (hSplit : corner1584_split_lift)
    (hNon : corner1584_nonsplit_shape) :
    ∀ lab : LargeEvenLabel, lab.tag = .twD → lab.rank = 3 →
      LargeEvenInLambda2 lab → LargeEvenLabelAll lab (fun R _ I _ => NoSetupAt R I) := by
  rintro ⟨tag, rank, n⟩ htag hr hlab
  simp only at htag hr
  subst htag
  subst hr
  have hΛ : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) :=
    ⟨hlab.1, by norm_num, fun h => absurd h (by norm_num)⟩
  have hne : (⟨.twA, 3, n⟩ : LargeEvenLabel) ≠ (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    intro h
    have h3 := congrArg LargeEvenLabel.rank h
    exact absurd h3 (show (3 : ℕ) ≠ 5 by norm_num)
  have h : LargeEvenLabelAll (⟨.twA, 3, n⟩ : LargeEvenLabel) (fun R _ I _ => NoSetupAt R I) :=
    noSetupAt_twA_of_leaves hSplit hNon hΛ rfl hne
  exact h

end S2MathAs3_1619Final

end
