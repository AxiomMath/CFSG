module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.RankThree.PartOne.MB3.OddOutLinear
import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.OutStructure (OutPNice)

theorem outPNice_three_of_isLieFam811 {X : Type} [Group X] {fam : LieFam811} {r f : ℕ}
    (h : IsLieFam811 X fam r f) : OutPNice 3 X := by
  cases fam with
  | psp6 =>
    obtain ⟨-, -, hm⟩ := h
    exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSp_ge_three_odd Nat.prime_three
      (by norm_num) le_rfl (hm.statedClassicalModel_of_ne_zero (by norm_num))
  | omega7 =>
    obtain ⟨-, -, -, hm⟩ := h
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaOdd_all Nat.prime_three
      (by norm_num) (hm.statedClassicalModel_of_ne_zero (by norm_num))
  | pomega8m =>
    obtain ⟨-, -, hm⟩ := h
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaMinus_all Nat.prime_three
      (by norm_num) (hm.statedClassicalModel_of_ne_zero (by norm_num))
  | l4 =>
    obtain ⟨-, -, hcase⟩ := h
    rcases hcase with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSL_ge_three_odd Nat.prime_three
        (by norm_num) (by norm_num) (hm.statedClassicalModel_of_ne_zero (by norm_num))
        (fun hd => absurd (hd.trans (Nat.gcd_dvd_left 4 _)) (by norm_num))
    · exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSU_odd Nat.prime_three
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
        (fun hd => absurd (hd.trans (Nat.gcd_dvd_left 4 _)) (by norm_num))
  | l6 =>
    obtain ⟨-, hcase⟩ := h
    rcases hcase with ⟨hmod, hm⟩ | ⟨hmod, hm⟩
    · exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSL_ge_three_odd Nat.prime_three
        (by norm_num) (by norm_num) (hm.statedClassicalModel_of_ne_zero (by norm_num))
        (fun hd => by have h3 := hd.trans (Nat.gcd_dvd_right 6 _); omega)
    · exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSU_odd Nat.prime_three
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
        (fun hd => by have h3 := hd.trans (Nat.gcd_dvd_right 6 _); omega)
  | l7 =>
    obtain ⟨-, hcase⟩ := h
    rcases hcase with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSL_ge_three_odd Nat.prime_three
        (by norm_num) (by norm_num) (hm.statedClassicalModel_of_ne_zero (by norm_num))
        (fun hd => absurd (hd.trans (Nat.gcd_dvd_left 7 _)) (by norm_num))
    · exact CFSG.RankThree.PartOne.OutStructure.outPNice_PSU_odd Nat.prime_three
        (hm.statedClassicalModel_of_ne_zero (by norm_num))
        (fun hd => absurd (hd.trans (Nat.gcd_dvd_left 7 _)) (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
