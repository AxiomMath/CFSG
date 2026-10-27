module

public import CFSG.RankThree.PartOne.FOCD.ClassicalOuter
public import CFSG.RankThree.PartOne.FOCD.ExcOuter
public import CFSG.RankThree.PartOne.FOCD.Exceptional

public section

namespace CFSG.RankThree.PartOne.FOCD

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)


theorem lieModel_cases {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ} (hp5 : 5 ≤ p)
    (hadm : StatedLieAdmissible t n p f) (h : LieModel G t n p f) :
    ((t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel G t n p f) ∨ (t ∈ chevalleyExceptionalTags ∧
        ChevalleyExceptionalModel G t p f) := by
  rcases h with ⟨ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, -⟩ | ⟨-, rfl, -⟩
  · left
    refine ⟨?_, hm⟩
    revert ht
    cases t <;> simp [classicalTags]
  · exact Or.inr ⟨ht, hm⟩
  · exfalso
    revert ht hadm
    cases t <;> simp [reeTitsTags, StatedLieAdmissible] <;> omega
  · exfalso
    simp only [StatedLieAdmissible] at hadm
    omega

section Certs


theorem defInnerComponent_of_certs : DefInnerComponent := by
  intro T _ _ t n f p hp hp5 hadm hs hmodel
  have := hs
  rcases lieModel_cases hp5 hadm hmodel with ⟨ht, hm⟩ | ⟨-, hm⟩
  · exact innerComp_classical hp hp5 hs ht hm
  · exact innerComp_of_noCompOf fun _ => noCompOf_exceptional hp hm

theorem defOuterComponent_of_certs : DefOuterComponent := by
  intro T _ _ t n f p hp hp5 hadm hs hmodel
  rcases lieModel_cases hp5 hadm hmodel with ⟨ht, hm⟩ | ⟨-, hm⟩
  · exact outerComp_classical hp hp5 hs ht hm
  · by_cases hcomm : ∀ a b : T, a * b = b * a
    · exact outerComp_of_comm hcomm
    · have hnab : ∃ a b : T, a * b ≠ b * a := by
        by_contra h
        exact hcomm fun a b => by_contra fun h' => h ⟨a, b, h'⟩
      exact outerComp_exceptional hp hp5 (center_eq_bot_of_nonab hs hnab) hm

end Certs

theorem defInnerComponent :
    DefInnerComponent := by
  exact defInnerComponent_of_certs

theorem defOuterComponent :
    DefOuterComponent := by
  exact defOuterComponent_of_certs

end CFSG.RankThree.PartOne.FOCD
