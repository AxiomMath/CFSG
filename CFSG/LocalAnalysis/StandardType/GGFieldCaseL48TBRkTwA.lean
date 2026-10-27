module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL48TB0TwConfigInputRest_of_twA (hB : GGTwE6ThreeBstarRankInput)
    (h : GGL48TB0TwConfigInputTwA) : GGL48TB0TwConfigInputRest := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hJD r hr hmark
  have hsplit : GGInnerDiagOnLab (fun p lab =>
      (lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1 ∧ lab.rank = r) ∨
        (GGTableBTwE6ThreeLabel p lab ∧ GGL48TB0Rank lab = r)) p Bs L := by
    refine GGInnerDiagOnLab.mono (fun p lab hP => ?_) hmark
    obtain ⟨hrow, hrk⟩ := hP
    by_cases hE : lab.tag = .twE6
    · rcases hrow with ⟨htag, -, -⟩ | hE6
      · exact absurd hE (by simp [htag])
      · exact Or.inr ⟨hE6, hrk⟩
    · rcases hrow with ⟨htag, hdr, hdq⟩ | ⟨htag, -, -⟩
      · exact Or.inl ⟨htag, hdr, hdq, by simpa [GGL48TB0Rank, hE] using hrk⟩
      · exact absurd htag hE
  rcases hsplit.elim_or with hA | hE
  · exact h G p B Bs x L D J X B₂ d y K U U₁ hS hJD r hr hA
  · have hm := hE
    obtain ⟨-, lab, -, hraw⟩ := hm
    obtain ⟨R, _, I, F, -, -, θ, ⟨⟨⟨htag, -, -⟩, hrk⟩, -⟩⟩ := largeEvenRawDatum_exists hraw
    have hr6 : r = 6 := by simpa [GGL48TB0Rank, htag] using hrk.symm
    subst hr6
    exact ggL48TwE6_pow_six_le_card hB hS.1.1 (GGInnerDiagOnLab.mono (fun _ _ hP => hP.1) hE)

end CFSG.StandardType

end
