module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150A10
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Rows
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Spor
public import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section K7


theorem k150For_a7 : K150For (alternatingGroup (Fin 7)) :=
  k150For_of_rows Sec4.Census.rank3II_4_2 (k150Rows_a7 k150Six_a7)

end K7

section K22


theorem k150For_m22 : K150For CFSG.Blueprint.NativeSporadic.M22 :=
  k150For_of_rows Sec4.Census.rank3II_4_2 (k150Rows_m22 k150Six_m22)

end K22

section T


theorem res1Thm150b_a7
    {P : ∀ (Y : Type) [Group Y], Prop} :
    Sylow155R1.Res1Thm150b (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  res1Thm150b_of_lists Sec4.diag_item41LargePrime_holds Sec11.Close.closed_sec4Item4_1ThreeCover
    Sec11.Close.closed_sec4Item4_5 Sec11.Close.closed_sec4Item4_8 k150For_a7 k150For_m22
    (fun _ _ h => Or.inl h) Sec14.Ronan149.item149S14_holds Sylow155R1.res1QE9_a7

theorem res1Thm150b_m22
    {P : ∀ (Y : Type) [Group Y], Prop} :
    Sylow155R1.Res1Thm150b (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P :=
  res1Thm150b_of_lists Sec4.diag_item41LargePrime_holds Sec11.Close.closed_sec4Item4_1ThreeCover
    Sec11.Close.closed_sec4Item4_5 Sec11.Close.closed_sec4Item4_8 k150For_a7 k150For_m22
    (fun _ _ h => Or.inr h) Sec14.Ronan149.item149S14_holds Sylow155R1.res1QE9_m22

end T

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
