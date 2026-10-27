module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieStep0
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF3Lin
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF3Uni
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF3PSp
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF3Omega7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieF3OmegaMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem exists3_of_isLieFam811 {X : Type} [Group X] [Finite X] {fam : LieFam811} {r f : ℕ}
    (h : IsLieFam811 X fam r f) : Exists3 X := by
  cases fam with
  | psp6 => exact exists3_psp6 h.1 h.2.1 h.2.2
  | omega7 => exact exists3_omega7 h.1 h.2.1 h.2.2.1 h.2.2.2
  | pomega8m => exact exists3_pomega8m h.1 h.2.1 h.2.2
  | l4 =>
    obtain ⟨hr, -, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := h
    · exact exists3_psl (by norm_num) hr hm fun hd =>
        absurd (hd.trans (Nat.gcd_dvd_left 4 _)) (by norm_num)
    · exact exists3_psu le_rfl hr hm fun hd =>
        absurd (hd.trans (Nat.gcd_dvd_left 4 _)) (by norm_num)
  | l6 =>
    obtain ⟨hr, ⟨hq, hm⟩ | ⟨hq, hm⟩⟩ := h
    · refine exists3_psl (by norm_num) hr hm fun hd => ?_
      have := hd.trans (Nat.gcd_dvd_right 6 _)
      omega
    · refine exists3_psu (by norm_num) hr hm fun hd => ?_
      have := hd.trans (Nat.gcd_dvd_right 6 _)
      omega
  | l7 =>
    obtain ⟨hr, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := h
    · exact exists3_psl (by norm_num) hr hm fun hd =>
        absurd (hd.trans (Nat.gcd_dvd_left 7 _)) (by norm_num)
    · exact exists3_psu (by norm_num) hr hm fun hd =>
        absurd (hd.trans (Nat.gcd_dvd_left 7 _)) (by norm_num)

theorem k2Lie_holds : K2Lie :=
  k2Lie_of_k2Simple (k2Simple_of_parts fun _ _ _ _ _ _ h =>
    ⟨outPNice_three_of_isLieFam811 h, exists3_of_isLieFam811 h, outerFixed3_of_isLieFam811 h⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
