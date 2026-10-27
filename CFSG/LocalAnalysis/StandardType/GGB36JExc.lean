module

public import CFSG.LocalAnalysis.StandardType.GGB36JExcE78
public import CFSG.LocalAnalysis.StandardType.GGB36JExcF4
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Core
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Hard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ltqJx_excB_of_excBS (h : GGK0ExcBS) : GGK0ExcB := by
  intro p lab hlab hpair Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hpair Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  exact ⟨D, hV, ha, hb, hc, hd, he⟩

theorem ggTablePKnownRK_b36JExc
    (hBS : GGK0ExcBS) (hβ : GGE6CoverThreeLocalRank) :
    GGTablePKnownRK GGRegimeB36JExc := by
  have hRE : GGK0CompREMult := ggK0CompREMult_of_excB (ltqJx_excB_of_excBS hBS)
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union
      (GGTablePKnownRK.union (ggTablePKnownRK_b36JExc_E78 ggE78LocalRankThree_holds)
        (ggTablePKnownRK_b36JExc_F4 hRE))
      (GGTablePKnownRK.union (ggTablePKnownRK_b36JExc_E6Core hRE)
        (ggTablePKnownRK_b36JExc_E6Hard hBS hβ))) ?_
  rintro p n labJ labX ⟨hJ, htag⟩
  by_cases hhard : (labX.tag = .E6 ∧ 3 ∣ 2 ^ labX.n - 1 ∧
      (labJ = ⟨.triD4, 0, labX.n⟩ ∨ labJ = ⟨.A, 2, 3 * labX.n⟩)) ∨
      (labX = ⟨.twE6, 0, 1⟩ ∧ labJ = ⟨.twA, 4, 1⟩)
  · exact Or.inr (Or.inr ⟨hJ, hhard⟩)
  · rcases htag with h | h | h | h | h
    · exact Or.inl (Or.inr ⟨hJ, h⟩)
    · exact Or.inr (Or.inl ⟨hJ, Or.inl h, hhard⟩)
    · exact Or.inr (Or.inl ⟨hJ, Or.inr h, hhard⟩)
    · exact Or.inl (Or.inl ⟨hJ, Or.inl h⟩)
    · exact Or.inl (Or.inl ⟨hJ, Or.inr h⟩)

end CFSG.StandardType

end
