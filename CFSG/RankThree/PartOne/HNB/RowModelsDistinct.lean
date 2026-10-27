module

public import CFSG.RankThree.PartOne.HNB.RowOrders
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartOne.KF.LayerModelRow

public section

namespace CFSG.RankThree.PartOne.HNB

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.S12K

theorem card_of_lieModel_table_of_ne_twistedF4
    {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ} (hT : RowTable t n) (hne : t ≠ .twistedF4)
    (h : LieModel S t n 2 f) :
    StatedLieAdmissible t n 2 f ∧ Nat.card S = charTwoOrder t n f := by
  rcases h with ⟨-, hc⟩ | ⟨rfl, ht, hm⟩ | ⟨rfl, ht, hm⟩ | ⟨rfl, rfl, hm⟩
  · refine ⟨hc.1, ?_⟩
    obtain ⟨h1, h2, h3, -, -⟩ := CFSG.Timmesfeld.card_statedClassicalModel_two hc
    rcases hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact h1 rfl
    · exact hc.2.elim
    · exact hc.2.elim
    · exact absurd rfl hne
    · exact h2 rfl
    · exact h3 rfl
  · refine ⟨hm.1, ?_⟩
    have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
    rcases hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    all_goals first | exact hc | exact absurd ht (by decide)
  · rcases hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    all_goals first | exact absurd ht (by decide) | exact absurd rfl hne
  · exact absurd hT (by simp [RowTable])

section Certified

theorem card_of_lieModel_table
    {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ} (hT : RowTable t n) (h : LieModel S t n 2 f) :
    StatedLieAdmissible t n 2 f ∧ Nat.card S = charTwoOrder t n f := by
  by_cases hF : t = .twistedF4
  · subst hF
    rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨rfl, -, hm⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact ⟨hm.1, card_of_reeTitsModel_twistedF4 hm⟩
    · exact absurd ht (by decide)
  · exact card_of_lieModel_table_of_ne_twistedF4 hT hF h

theorem rowModelsDistinct_holds :
    RowModelsDistinct := by
  intro S _ t t' n n' f f' hT hT' hsp hm hm'
  obtain ⟨hadm, hc⟩ := card_of_lieModel_table hT hm
  obtain ⟨hadm', hc'⟩ := card_of_lieModel_table hT' hm'
  have heq : charTwoOrder t n f = charTwoOrder t' n' f' := hc.symm.trans hc'
  rcases hsp with hs | hs
  · obtain ⟨h1, h2, h3⟩ := rigid_special hs hT' hadm hadm' heq.symm
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  · exact rigid_special hs hT hadm' hadm heq

end Certified

end CFSG.RankThree.PartOne.HNB
