module

public import CFSG.LocalAnalysis.WeakClosure81.W16LAutFaith
public import CFSG.LocalAnalysis.WeakClosure81.W16LAutDih
public import CFSG.LocalAnalysis.WeakClosure81.TwelveRankOne
public import CFSG.ClassicalGroups.Unitary.ThreeEven
public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

theorem autRank166Input_holds : AutRank166Input := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X _ _ Y n hn hY hYe hX E hE hEY
    rcases rankOne_benderType hX with hB | hB
    all_goals
      exact (hB.card_le_of_sq_eq_one_aut E fun x hx => by
        simpa [pow_two] using hE.2 x hx).2 (by decide)
  · intro X _ _ Y n hn hY hYe hX E hE hEY
    haveI : Group.IsPerfect X := ⟨hX.1⟩
    exact CFSG.ClassicalGroups.Unitary.card_le_of_isElemAbelian_mulAut_of_lieModel_psu3 hX.2.1 E hE
  · intro X _ _ Y hY hYe hgen hp E hE hEY
    exact autRank166_dih Y hY hgen hp E hE hEY
  · intro X _ _ Y n hn hY hYe hX α hαY hα
    rcases hX with h | h | h
    · exact autRank166_faith_psl hn hY hYe h α hα
    · exact autRank166_faith_sz hn hY hYe h α hα
    · exact autRank166_faith_u3 hn hY hYe h α hα

end CFSG.LocalAnalysis.WeakClosure81

end
