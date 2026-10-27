module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisTriD4Three
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTriD4Outer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLangAxisOn_t3_of_inner
    (hsub : GGNbrSubcomponentInput) (hKG : GGTriD4KnownInput) (hL : GGTriD4StdSubInput)
    (hE6 : GGTwE6LocalRankInput)
    (h1 : GGNbrLangAxisInnerOn fun p lab => GGNbrLangT3Label p lab ∧ lab.n = 1)
    (he : GGNbrLangAxisInnerOn fun p lab => GGNbrLangT3Label p lab ∧ 3 ∣ 2 ^ lab.n - 1) :
    GGNbrLangAxisOn GGNbrLangT3Label := by
  have hI : GGNbrLangAxisInnerOn fun p lab =>
      GGNbrLangT3Label p lab ∧ (lab.n = 1 ∨ 3 ∣ 2 ^ lab.n - 1) :=
    (h1.or he).mono fun _ _ ⟨ht, h⟩ => h.elim (fun h => Or.inl ⟨ht, h⟩) fun h => Or.inr ⟨ht, h⟩
  have hO : GGNbrLangAxisOuterOn fun p lab =>
      GGNbrLangT3Label p lab ∧ (lab.n = 1 ∨ 3 ∣ 2 ^ lab.n - 1) :=
    (ggNbrLangAxisOuterOn_t3 hsub hKG hL hE6).mono fun _ _ h => h.1
  refine ((ggNbrLangAxisOn_of_inner_outer hI hO).or ggNbrLangAxisOn_nsTriD4Three).mono
    fun p lab ht => ?_
  by_cases hns : 2 ≤ lab.n ∧ ¬ 3 ∣ 2 ^ lab.n - 1
  · exact Or.inr ⟨ht.1, ht.2, hns.1, hns.2⟩
  · refine Or.inl ⟨ht, ?_⟩
    by_cases h3 : 3 ∣ 2 ^ lab.n - 1
    · exact Or.inr h3
    · refine Or.inl ?_
      have hn : lab.n ≤ 1 := by
        by_contra h
        exact hns ⟨by omega, h3⟩
      interval_cases h : lab.n
      · exact absurd (by norm_num) h3
      · rfl

end CFSG.StandardType
