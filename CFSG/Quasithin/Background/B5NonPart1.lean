module

public import CFSG.Quasithin.Background.B5Part1
public import CFSG.Quasithin.Background.B5NonId

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

section Induction

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem part1_of_cases (h : B51Hyp G L)
    (hcases : B51Case1ii G L ∨ (∃ n, B51Case1iii G L n) ∨ B51Case1iv G L) : B51Part1 G L := by
  have hGL : G = L := by
    rcases hcases with h2 | ⟨n, h3⟩ | h4
    · exact h2.1
    · exact h3.1
    · exact h4.1
  refine ⟨genFitting_eq_of_eq h hGL, ?_⟩
  rcases hcases with h2 | ⟨n, h3⟩ | h4
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl ⟨n, h3⟩))
  · exact Or.inr (Or.inr (Or.inr h4))

theorem part1_of_nonirr' (hSL3 : AsB51NonirrSL3) (hLn : AsB51NonirrLn) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) (hT : IsL345Type ↥L) : B51Part1 G L := by
  refine part1_of_cases h ?_
  rcases hT with ⟨n, K, hK, hf, hc, ⟨e⟩⟩ | ⟨K, hK, hf, hc, ⟨e⟩⟩ | ⟨K, hK, hf, hc, ⟨e⟩⟩
  · exact Or.inl (hSL3 V hV G L h hU ⟨n, K, hK, hf, hc, ⟨e⟩⟩)
  · rcases hLn V hV G L h hU (Or.inl ⟨K, hK, hf, hc, ⟨e⟩⟩) with h3 | h4
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)
  · rcases hLn V hV G L h hU (Or.inr ⟨K, hK, hf, hc, ⟨e⟩⟩) with h3 | h4
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)

end Induction

theorem part1_below (hI : B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (hSL3 : AsB51NonirrSL3)
    (hLn : AsB51NonirrLn) : ∀ N, B51Part1Below N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ hVN hV G L h
    by_cases hU : commV L ∈ IrrPlus L ⊤
    · exact part1_of_irr hI hV h hU
    · have hIH : B51Part1Below (Nat.card V) := ih (Nat.card V) hVN
      exact part1_of_nonirr' hSL3 hLn hV h hU (nonirr_identify hA21 hI.b42 hA36 hIH hV h hU)

theorem b51_part1' (hI : B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover) (hSL3 : AsB51NonirrSL3)
    (hLn : AsB51NonirrLn) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (h : B51Hyp G L) : B51Part1 G L :=
  part1_below hI hA21 hA36 hSL3 hLn (Nat.card V + 1) V (Nat.lt_succ_self _) hV G L h

end B5

end CFSG.Quasithin
