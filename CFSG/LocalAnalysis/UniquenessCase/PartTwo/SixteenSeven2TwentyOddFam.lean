module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s16c167_oddCore_isSym {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n) (h : IsSym X n) :
    CFSG.oddCore X = ⊥ := by
  obtain ⟨e⟩ := h
  refine oddCore_eq_bot_of_mulEquiv e.symm ?_
  refine (CFSG.ComponentClassification.SmallLocal.symmetric_group_odd_core (Fin n)).2 ?_
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

theorem s16c167_oddCore_isLn {X : Type} [Group X] {m : ℕ} (h3 : 3 ≤ m) (h5 : m ≤ 5)
    (h : IsLn X m 1) : CFSG.oddCore X = ⊥ := by
  have hs : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hc : Nat.card X = 168 ∨ Nat.card X = 20160 ∨ Nat.card X = 9999360 := by
    interval_cases m
    · exact Or.inl (CFSG.Blueprint.LieModel.card_psl_three_two h)
    · exact Or.inr (Or.inl (StatedAPI.card_of_statedClassicalModel_psl_four_two
        (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))))
    · exact Or.inr (Or.inr (StatedAPI.card_of_statedClassicalModel_psl_five_two
        (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))))
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rcases hc with h | h | h <;> omega)
  exact oddCore_eq_bot_of_isSimpleGroup (by rcases hc with h | h | h <;> rw [h] <;> decide)

theorem s16c167_oddCore_isSpn {X : Type} [Group X] (h : IsSpn X 6 1) :
    CFSG.oddCore X = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact oddCore_eq_bot_of_mulEquiv e.symm
    (oddCore_statedSp_eq_bot_of_card_eq_two (r := 6 / 2) (by norm_num)
      (by rwa [pow_one] at hK))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
