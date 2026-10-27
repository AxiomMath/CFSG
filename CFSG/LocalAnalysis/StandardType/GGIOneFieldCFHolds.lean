module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreField
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFTypeA
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFTwD
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstarE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Holds


theorem largeEvenLabelAll_innerDiagBound_field {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  rcases h with ⟨ht, hpn, hpl, -⟩ | ⟨ht, hl, hle, hpn, -⟩ | ⟨ht, hpn, hp3, -⟩ | ⟨ht, hpn, -⟩
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hpn hpl
    subst ht
    have hl1 : 1 ≤ l := hlab.2.1
    intro Q hQ
    exact recipeLinear_innerDiagBound_dvd hp hpn (by omega) hpl hQ
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl hle hpn
    subst ht
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · have hmo : Odd (l - 1) := by
        obtain ⟨k, hk⟩ := hle
        exact ⟨k - 1, by omega⟩
      exact IOneFieldCF.recipeOmegaMinus_innerDiagBound hp hpn (by omega) hmo hQ
  · exact largeEvenLabelAll_innerDiagBound_excLSplitE6 hp hlab ⟨ht, hp3, hpn⟩
  · exact largeEvenLabelAll_innerDiagBound_excLSplit hp hlab ⟨ht, hpn⟩

theorem ggIOneMoreFieldCorFourTwoInput_holds : GGIOneMoreFieldCorFourTwoInput :=
  fun _ _ hp hlab h => largeEvenLabelAll_innerDiagBound_field hp hlab h

end Holds

end CFSG.StandardType
