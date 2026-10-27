module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Red
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Harris

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

open Subgroup CFSG.Blueprint

@[expose] def U43NoOrder27Statement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 → ∀ g : S, orderOf g ≠ 27

@[expose] def U43Cent5Statement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 →
    ∀ x : S, orderOf x = 5 → Nat.card (centralizer ({x} : Set S)) ∣ 5

@[expose] def U43Norm7Statement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 →
    ∀ P : Subgroup S, Nat.card P = 7 → Nat.card (normalizer (P : Set S)) ∣ 21

@[expose] def U43Cent9Statement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 4 3 1 →
    ∀ g : S, orderOf g = 9 → IsPGroup 3 (centralizer ({g} : Set S))

theorem s16kU43SubgroupNoncyclic3_of_facts (h27 : U43NoOrder27Statement)
    (h5 : U43Cent5Statement) (h7 : U43Norm7Statement) (h9 : U43Cent9Statement) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16kU43SubgroupNoncyclic3 := by
  intro S _ _ hL X hX
  have hF : U43CentFacts S :=
    { card := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.s3h_card_U43 hL
      not27 := h27 S hL
      cent5 := h5 S hL
      norm7 := h7 S hL
      cent9 := h9 S hL }
  exact noncyclic3_of_facts hF.toCountingFacts X hX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

