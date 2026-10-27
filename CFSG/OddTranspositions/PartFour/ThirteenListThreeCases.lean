module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListThreeTranspCases
import CFSG.OddTranspositions.PartFour.ThirteenListThree
import CFSG.OddTranspositions.PartFour.ThirteenListThreeRefl
import CFSG.OddTranspositions.PartFour.ThirteenListThreeSix
import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListDerivedCases

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 CFSG.Open


theorem oddTranspListDerivedEqThreeTransp_of_cases
    (hCover : OddTranspListThreeTranspReflSixCover)
    (hLift : OddTranspListThreeTranspReflLift) (hFi : OddTranspListThreeTranspFischer) :
    OddTranspListDerivedEqThreeTransp := by
  have hQuot := oddTranspListThreeTranspReflSixQuot_holds
  intro X _ _ s hs hodd hncl hO2 hOZ hder h3
  obtain ⟨hP, hZ, hS⟩ := hyp_quotient_center hodd hncl hO2 hOZ hder h3
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned (X ⧸ Subgroup.center X)
      _ hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS with
    ⟨m, -, φ, hφ⟩ | ⟨m, -, b, halt, hnd, hM⟩ | ⟨m, hm, Q, hnd, hex, hM⟩ | ⟨m, hm, hM⟩ |
      ⟨m, hm, f, hsym, hnd, hM⟩ | hFi22 | hFi23 | hFi24
  · exact oddTranspListAlt_of_perm hO2 hOZ φ hφ
  · exact oddTranspListAlt_of_fischerSp b halt hnd hM
  · exact oddTranspListAlt_of_fischerOrth hm Q hnd hex hM
  · exact oddTranspListAlt_of_fischerSU hm hM
  · rcases (show m = 5 ∨ m = 6 ∨ 7 ≤ m by omega) with rfl | rfl | h7
    · exact oddTranspListAlt_of_f3Five hsym hnd hM
    · by_cases hZX : Subgroup.center X = ⊥
      · by_cases hZR : Subgroup.center ↥(Subgroup.closure (fischerTransvections
            (fun x y => f x y) fun v => f v v = 1)) = ⊥
        · exact oddTranspListAlt_of_reflSix_center hZX hs2 hsym hnd hZR hM
        · exact hQuot X s hs hodd hncl hO2 hOZ hder h3 hZX f hsym hnd hZR hM
      · rcases center_eq_bot_or_anisotropic_of_reflSix hs2 hncl hO2 hder hS ⟨hsym, hnd⟩
          hM.choose with h | h
        · exact absurd h hZX
        · exact hCover X s hs hodd hncl hO2 hOZ hder h3 hZX f hsym hnd h hM
    · by_cases hZX : Subgroup.center X = ⊥
      · exact oddTranspListAlt_of_reflSeven hZX h7 hsym hnd hM
      · exact hLift X s hs hodd hncl hO2 hOZ hder h3 hZX m h7 f hsym hnd hM
  · exact hFi X s hs hodd hncl hO2 hOZ hder h3 (Or.inl hFi22)
  · exact hFi X s hs hodd hncl hO2 hOZ hder h3 (Or.inr (Or.inl hFi23))
  · exact hFi X s hs hodd hncl hO2 hOZ hder h3 (Or.inr (Or.inr hFi24))

end CFSG.OddTranspositions.PartFour
