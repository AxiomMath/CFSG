module

import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddUnitary
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddOrthogonal
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddChevalley
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddTwisted
import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint
open CFSG.Blueprint.Multiplier (genericOrders)

theorem fieldAutOdd_remainingClassical_subfield {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f r : ℕ}
    (ht : t = .PSU ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : LieModel X t n p f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrg : ¬ r ∣ (genericOrders t n p f).1) (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧
      LieModel Y t n p (f / r) := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact fieldAutOdd_psu_subfield hp hp2 hX hr hr5 hrg θ hθ hout
  · exact fieldAutOdd_pomegaOdd_subfield hp hp2 hX hr hr5 θ hθ hout
  · exact fieldAutOdd_pomegaPlus_subfield hp hX hr hr5 θ hθ hout
  · exact fieldAutOdd_pomegaMinus_subfield hp hX hr hr5 θ hθ hout

theorem fieldAutOdd_of_classical_subfield {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n p e : ℕ} (ht : t ∈ classicalTags) (hp2 : p ≠ 2)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (θ : MulAut X) {Y : Subgroup X}
    (hY : Y ≤ signalizerFixedSubgroup θ) (hmodel : LieModel Y t n p e) :
    ∃ S : Subgroup X, S ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup S ∧
      2 ≤ CFSG.pRank p S := by
  refine ⟨Y, hY, hmodel.isSimpleGroup_of_mem_classicalTags ht, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  obtain ⟨-, he, hrank⟩ := CFSG.SectionRank.classical_model_rank hp2
    (hmodel.statedClassicalModel ht)
  rcases hrank with ⟨ht, (⟨hn, h⟩ | ⟨-, h⟩ | h)⟩ | ⟨-, (⟨-, h⟩ | h)⟩ |
      ⟨-, (⟨-, h⟩ | h)⟩ | h
  · exact (hA1 ⟨ht, hn⟩).elim
  all_goals omega


theorem fieldAutOdd_exceptional {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f r : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : LieModel X t n p f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
      2 ≤ CFSG.pRank p Y := by
  have hmodel := hX.chevalleyExceptionalModel ht
  cases t with
  | G2 =>
    exact fieldAutOdd_untwisted (Or.inl rfl) hp hp2 hadm.2.1 hmodel.2
      hr hr5 θ hθ hout
  | F4 =>
    exact fieldAutOdd_untwisted (Or.inr (Or.inl rfl)) hp hp2 hadm.2.1 hmodel.2
      hr hr5 θ hθ hout
  | E6 =>
    exact fieldAutOdd_untwisted (Or.inr (Or.inr (Or.inl rfl))) hp hp2 hadm.2.1 hmodel.2
      hr hr5 θ hθ hout
  | E7 =>
    exact fieldAutOdd_untwisted (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      hp hp2 hadm.2.1 hmodel.2 hr hr5 θ hθ hout
  | E8 =>
    exact fieldAutOdd_untwisted (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      hp hp2 hadm.2.1 hmodel.2 hr hr5 θ hθ hout
  | twistedE6 => exact fieldAutOdd_twistedE6 hp hadm hX hr hr5 θ hθ hout
  | trialityD4 => exact fieldAutOdd_trialityD4 hp hadm hX hr hr5 θ hθ hout
  | _ => simp [chevalleyExceptionalTags] at ht

end CFSG.LocalAnalysis.UniquenessCase.UC22
