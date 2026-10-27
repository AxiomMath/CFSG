module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem gapOutU43_le_eight : ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 →
    ∀ E : Subgroup (MulAut S), (∀ a ∈ E, a ^ 2 = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ∈ (MulAut.conj : S →* MulAut S).range → a = 1) → Nat.card E ≤ 8 := by
  intro S _ _ hLie E _ _ hEinn
  have hcl : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 4 3 1 :=
    hLie.statedClassicalModel (by decide)
  have hcard :=
    (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound S 4 3 1 hcl).2.2.1
  norm_num at hcard
  haveI : Finite (Outer S) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let φ : E →* Outer S := (QuotientGroup.mk' (inner S)).comp E.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : MulAut S) ∈ inner S := (QuotientGroup.eq_one_iff (a : MulAut S)).1 ha
    exact Subtype.ext (hEinn a a.2 h1)
  calc Nat.card E ≤ Nat.card (Outer S) := Nat.card_le_card_of_injective φ hφ
    _ = 8 := hcard

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
