module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoLiftSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLESixTwo
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLExcVacuity
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLFFourTwo
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAClassical
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLLinTwoAPair
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLLinTwoDPair
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLThreeAdicCells
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTwDTwo
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTwF4Cells
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCells
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCubic

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem split_three_of_dvd_add_one_dispatch {lab : LargeEvenLabel}
    (hs : LargeEvenSplit 3 lab) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    (¬ LargeEvenUntwisted lab.tag ∧ lab.tag ≠ .triD4) ∨ lab.n = 1 := by
  have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  rcases hs with ⟨-, h⟩ | ⟨hu, ht, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · exact Or.inl ⟨hu, ht⟩
  · omega
  · exact Or.inr h


theorem ggInndiagOnCompAt_pairs_split :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
      3 ∣ 2 ^ lab.n + 1 → GGNoThreeCenter lab → lab.tag ≠ .E7 → lab.tag ≠ .E8 →
      lab.tag ≠ .twB2 → lab.tag ≠ .B2der → lab.tag ≠ .G2der → lab.tag ≠ .twF4der →
      (lab.tag = .A → lab.rank + 1 ≤ 9) → (lab.tag = .twA → lab.rank + 1 ≤ 6) →
      (lab.tag = .B ∨ lab.tag = .C → lab.rank ≤ 5) →
      (GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩) ∧
        GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ := by
  intro lab hlab hsplit h3 h3c h7 h8 hb hb' hg hf hA hU _
  have hq := split_three_of_dvd_add_one_dispatch hsplit h3
  obtain ⟨tag, r, g⟩ := lab
  cases tag
  case A =>
    have hn : g = 1 := hq.resolve_left fun h => h.1 trivial
    exact ⟨ggInndiagOnCompAt_A_two_dPair hlab rfl hn (hA rfl),
      ggInndiagOnCompAt_A_two_aPair hlab rfl hn (hA rfl)⟩
  case twA =>
    have hr : (LargeEvenLieTag.twA = .twA ∧ r ≤ 5) ∨ (LargeEvenLieTag.twA = .twD ∧ r = 3) :=
      Or.inl ⟨rfl, by have := hU rfl; dsimp only at this; omega⟩
    exact ⟨ggInndiagOnCompAt_unitary_dPair hlab hr, ggInndiagOnCompAt_unitary_aPair hlab hr⟩
  case B => exact ggInndiagOnCompAt_pairs_classical hlab (Or.inl rfl) h3
  case C => exact ggInndiagOnCompAt_pairs_classical hlab (Or.inr (Or.inl rfl)) h3
  case D =>
    have hr3 : 3 ≤ r := hlab.2
    by_cases hr : r = 3
    · subst hr
      have hn : g = 1 := hq.resolve_left fun h => h.1 trivial
      exact ⟨ggInndiagOnCompAt_D_three_two_dPair hlab rfl rfl hn,
        ggInndiagOnCompAt_D_three_two_aPair hlab rfl rfl hn⟩
    · exact ggInndiagOnCompAt_pairs_classical hlab
        (Or.inr (Or.inr (Or.inl ⟨rfl, by dsimp only; omega⟩))) h3
  case twD =>
    have hr2 : 2 ≤ r := hlab.2
    rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr
    · exact ⟨ggInndiagOnCompAt_twD_two_dPair hlab rfl rfl,
        ggInndiagOnCompAt_twD_two_aPair hlab rfl rfl⟩
    · exact ⟨ggInndiagOnCompAt_unitary_dPair hlab (Or.inr ⟨rfl, rfl⟩),
        ggInndiagOnCompAt_unitary_aPair hlab (Or.inr ⟨rfl, rfl⟩)⟩
    · exact ggInndiagOnCompAt_pairs_classical hlab (Or.inr (Or.inr (Or.inr ⟨rfl, hr⟩))) h3
  case G2 =>
    have hn : g = 1 := hq.resolve_left fun h => h.1 trivial
    have h2 : 2 ≤ g := hlab.2.2
    omega
  case F4 =>
    have hn : g = 1 := hq.resolve_left fun h => h.1 trivial
    exact ⟨ggInndiagOnCompAt_or (ggInndiagOnCompAt_D4_threeAdic hlab (Or.inl rfl) h3)
      (ggInndiagOnCompAt_F4_two_triD4 rfl hn), ggInndiagOnCompAt_F4_two_aPair hlab rfl hn⟩
  case E6 =>
    have hn : g = 1 := hq.resolve_left fun h => h.1 trivial
    exact ⟨ggInndiagOnCompAt_or (ggInndiagOnCompAt_D4_threeAdic hlab (Or.inr rfl) h3)
      (ggInndiagOnCompAt_E6_two_triD4 rfl hn), ggInndiagOnCompAt_E6_two_aPair rfl hn⟩
  case twE6 => exact absurd h3 h3c
  case triD4 =>
    have hn : g = 1 := hq.resolve_left fun h => h.2 rfl
    refine ⟨ggInndiagOnCompAt_of_noJ1 hlab (fun n => n)
      (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
      (largeEvenLabelAll_noJ1_dPair_exc hlab (Or.inr (Or.inl rfl))),
      ggInndiagOnCompAt_of_noJ1 hlab (fun n => 3 * n)
      (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
      (largeEvenLabelAll_noJ1_aPair_exc hlab (Or.inr (Or.inl rfl)) ?_)⟩
    dsimp only
    rw [hn]
    decide
  case twF4 => exact ⟨ggInndiagOnCompAt_twF4 hlab rfl _, ggInndiagOnCompAt_twF4 hlab rfl _⟩
  case E7 => exact absurd rfl h7
  case E8 => exact absurd rfl h8
  case twB2 => exact absurd rfl hb
  case B2der => exact absurd rfl hb'
  case G2der => exact absurd rfl hg
  case twF4der => exact absurd rfl hf

theorem ggTwE6OfOutsideSplitKnown_holds : GGTwE6OfOutsideSplitKnown :=
  ggTwE6OfOutsideSplitKnown_of_noLift ggUnitaryCubicKnown_holds ggInndiagOnCompAt_pairs_split

end CFSG.StandardType.SCFourCover

end
