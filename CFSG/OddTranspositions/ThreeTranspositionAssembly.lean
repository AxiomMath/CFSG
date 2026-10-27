module

public import CFSG.OddTranspositions.ClassificationStatement
public import CFSG.OddTranspositions.SymSixQHyp
public import CFSG.OddTranspositions.SymThreeNoSqE1
public import CFSG.OddTranspositions.SpQHyp
public import CFSG.OddTranspositions.UPQHyp
public import CFSG.OddTranspositions.OrthNoSqE1
public import CFSG.OddTranspositions.FiNoSqE1

public section

namespace CFSG.OddTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer.Classification

theorem threeTranspositionDichotomy_of_f3Row
    (hF3 : F3Row) : ThreeTranspositionDichotomy := by
  intro G _ D hP hZ hS
  haveI : Finite G := hP.1
  by_cases hab : ∀ a b : commutator G, a * b = b * a
  · obtain ⟨φ, hφ⟩ := CFSG.Fischer.Classification.Pair.exists_mulEquiv_perm_three hP hZ hS hab
    exact Or.inl (noSqE1_of_pair_perm_three hP φ hφ)
  · push_neg at hab
    have h := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned
      G D hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS
    rcases h with
      ⟨m, hm, φ, hφ⟩ | ⟨m, hm, b, hskew, hnd, hM⟩ | ⟨m, hm, Q, hnd, hex, hM⟩ |
        ⟨m, hm, hM⟩ | ⟨m, hm, f, hsymm, hnd, hM⟩ | ⟨φ, -, -⟩ | ⟨φ, -, -⟩ | ⟨φ, -, -⟩
    · rcases hm with rfl | hm5
      · exact Or.inl (noSqE1_of_pair_perm_three hP φ hφ)
      · by_cases hm6 : m = 6
        · subst m
          exact Or.inr (transvectionHyp_of_perm_six hP hZ hS hab φ hφ)
        · exact Or.inl (noSqE1_of_pair_perm_of_ne_six hP hZ (by omega) φ hφ)
    · exact Or.inr (transvectionHyp_of_symp hP hZ hS hab hm hskew hnd hM)
    · exact Or.inl (noSqE1_of_orth hP hZ hm Q hnd hex hM)
    · exact Or.inr (transvectionHyp_of_psu hP hZ hS hab hm hM)
    · exact hF3 G hP hZ hS m hm f hsymm hnd hM
    · exact Or.inl (noSqE1_of_fi22 hP hZ hS hab ⟨φ⟩)
    · exact Or.inl (noSqE1_of_fi23 hP hZ hS hab ⟨φ⟩)
    · exact Or.inl (noSqE1_of_fi24 hP hZ hS hab ⟨φ⟩)

end CFSG.OddTranspositions
