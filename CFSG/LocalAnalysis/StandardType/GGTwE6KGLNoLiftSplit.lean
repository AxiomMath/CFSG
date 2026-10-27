module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLSplitDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLKnownInputs
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverSetting
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLSmall
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGLayerTitsCent
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusTypeAPlus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusSymplectic

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggTwE6OfOutsideSplitKnown_of_at
    (h : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
      GGTwE6OfOutsideAt lab) :
    GGTwE6OfOutsideSplitKnown := by
  intro lab hlab hsplit
  refine LargeEvenLabelAll.mono ?_ (h lab hlab hsplit)
  rintro R _ _ _ hR hs hna L' _ _ ψ hψ hker hL s t n hs3 ht3 hst ⟨φs, hφsI, hφs⟩
    ⟨φt, hφtI, hφt⟩ hn J₁ hJ₁ hmark hout
  have hfin : Finite R := Finite.of_surjective ψ hψ
  have hJ := commutator_eq_self_of_isComponentOf hJ₁
  exact hR hs hna hfin φs φt n
    ((induced_eq_one_iff hψ hker hL (TypeA.induced_pow ψ hφs 3)).2 hs3)
    ((induced_eq_one_iff hψ hker hL (TypeA.induced_pow ψ hφt 3)).2 ht3)
    ((induced_commute_iff hψ hker hL hφs hφt).2 hst) hφsI hφtI hn (J₁.map ψ)
    ((isComponentOf_map_iff hψ hker hφs hJ).1 hJ₁) ((largeEvenMarking_map_iff hker hJ _).1 hmark)
    ((ggOutsideInndiag_map_iff hker hφt hJ).1 hout)

private theorem not_three_dvd_add_one_of_sub_one {m : ℕ} (h : 3 ∣ m - 1) : ¬ 3 ∣ m + 1 := by
  omega


private theorem ggTwE6OfOutsideAt_of_torusLift_of_three_dvd {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : 3 ∣ 2 ^ lab.n + 1 → LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R) :
    GGTwE6OfOutsideAt lab := by
  by_cases h3 : 3 ∣ 2 ^ lab.n + 1
  · exact ggTwE6OfOutsideAt_of_torusLift (h h3)
  · exact ggTwE6OfOutsideAt_of_three_dvd hlab fun h3' => absurd h3' h3

theorem ggTwE6OfOutsideAt_of_noLiftSplit (hUCUB : GGUnitaryCubicKnown)
    (hNo : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
      3 ∣ 2 ^ lab.n + 1 → GGNoThreeCenter lab → lab.tag ≠ .E7 → lab.tag ≠ .E8 →
      lab.tag ≠ .twB2 → lab.tag ≠ .B2der → lab.tag ≠ .G2der → lab.tag ≠ .twF4der →
      (lab.tag = .A → lab.rank + 1 ≤ 9) → (lab.tag = .twA → lab.rank + 1 ≤ 6) →
      (lab.tag = .B ∨ lab.tag = .C → lab.rank ≤ 5) →
      (GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩) ∧
        GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hsplit : LargeEvenSplit 3 lab) :
    GGTwE6OfOutsideAt lab := by
  have hN : GGNoThreeCenter lab → lab.tag ≠ .E7 → lab.tag ≠ .E8 → lab.tag ≠ .twB2 →
      lab.tag ≠ .B2der → lab.tag ≠ .G2der → lab.tag ≠ .twF4der → GGTwE6OfOutsideAt lab := by
    intro h3c h7 h8 hb hb' hg hf
    by_cases hA : lab.tag = .A ∧ 10 ≤ lab.rank + 1
    · exact ggTwE6OfOutsideAt_of_torusLift_of_three_dvd hlab fun h3 =>
        largeEvenLabelAll_torusLift_typeAPlus_threeFive hA.1 h3 hA.2
    by_cases hU : lab.tag = .twA ∧ 7 ≤ lab.rank + 1
    · exact ggTwE6OfOutsideAt_of_torusLift_of_three_dvd hlab fun h3 =>
        largeEvenLabelAll_torusLift_twA_threeFive hlab hU.1 h3 hU.2
    by_cases hS : (lab.tag = .B ∨ lab.tag = .C) ∧ 6 ≤ lab.rank
    · exact ggTwE6OfOutsideAt_of_torusLift
        (largeEvenLabelAll_torusLift_symplectic_threeFive hS.1 hS.2)
    have key := fun h3 => hNo lab hlab hsplit h3 h3c h7 h8 hb hb' hg hf
      (fun ht => by have := not_and.mp hA ht; omega)
      (fun ht => by have := not_and.mp hU ht; omega)
      (fun ht => by have := not_and.mp hS ht; omega)
    exact ggTwE6OfOutsideAt_of_inndiagOnCompAt hlab (fun h3 => (key h3).1) (fun h3 => (key h3).2)
  have hT := ggTitsThreeCentInput_holds
  obtain ⟨tag, r, g⟩ := lab
  cases tag
  case twB2 => exact ggTwE6OfOutsideAt_small hT hlab (Or.inl rfl)
  case B2der => exact ggTwE6OfOutsideAt_small hT hlab (Or.inr (Or.inl rfl))
  case G2der => exact ggTwE6OfOutsideAt_small hT hlab (Or.inr (Or.inr (Or.inl rfl)))
  case twF4der => exact ggTwE6OfOutsideAt_small hT hlab (Or.inr (Or.inr (Or.inr rfl)))
  case E7 =>
    rcases three_dvd_two_pow_add_one_or_sub_one g with h | h
    · exact ggTwE6OfOutsideAt_of_torusLift
        (largeEvenLabelAll_torusLift_excPlus_threeFive (Or.inl rfl) h)
    · exact ggTwE6OfOutsideAt_of_torusLift
        (largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inl rfl) h)
  case E8 =>
    rcases three_dvd_two_pow_add_one_or_sub_one g with h | h
    · exact ggTwE6OfOutsideAt_of_torusLift
        (largeEvenLabelAll_torusLift_excPlus_threeFive (Or.inr rfl) h)
    · exact ggTwE6OfOutsideAt_of_torusLift
        (largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inr rfl) h)
  case twE6 =>
    by_cases h : 3 ∣ 2 ^ g + 1
    · exact ggTwE6OfOutsideAt_twE6 rfl h
    · exact hN h (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  case E6 =>
    by_cases h : 3 ∣ 2 ^ g - 1
    · exact ggTwE6OfOutsideAt_of_torusLift (largeEvenLabelAll_torusLift_E6_three rfl h)
    · exact hN h (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  case A =>
    by_cases h : 3 ∣ r + 1 ∧ 3 ∣ 2 ^ g - 1
    ·
      exact ggTwE6OfOutsideAt_of_three_dvd hlab fun hodd =>
        absurd hodd (not_three_dvd_add_one_of_sub_one h.2)
    · exact hN h (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  case twA =>
    by_cases h : 3 ∣ r + 1 ∧ 3 ∣ 2 ^ g + 1
    · by_cases hr : r = 2 ∨ r = 5
      ·
        exact ggTwE6OfOutsideAt_of_three_dvd hlab fun hodd =>
          hUCUB _ hlab hodd rfl hr fun hn => hn h
      · exact ggTwE6OfOutsideAt_of_torusLift
          (largeEvenLabelAll_torusLift_twA_threeFive hlab rfl h.2 (by dsimp only; omega))
    · exact hN h (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  all_goals
    exact hN trivial (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

theorem ggTwE6OfOutsideSplitKnown_of_noLift (hUCUB : GGUnitaryCubicKnown)
    (hNo : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
      3 ∣ 2 ^ lab.n + 1 → GGNoThreeCenter lab → lab.tag ≠ .E7 → lab.tag ≠ .E8 →
      lab.tag ≠ .twB2 → lab.tag ≠ .B2der → lab.tag ≠ .G2der → lab.tag ≠ .twF4der →
      (lab.tag = .A → lab.rank + 1 ≤ 9) → (lab.tag = .twA → lab.rank + 1 ≤ 6) →
      (lab.tag = .B ∨ lab.tag = .C → lab.rank ≤ 5) →
      (GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩) ∧
        GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩) :
    GGTwE6OfOutsideSplitKnown :=
  ggTwE6OfOutsideSplitKnown_of_at fun _ hlab hsplit =>
    ggTwE6OfOutsideAt_of_noLiftSplit hUCUB hNo hlab hsplit

end CFSG.StandardType.SCFourCover

end
