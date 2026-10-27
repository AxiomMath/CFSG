module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E9

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S

section Rows


theorem rowOf427_ru
    : RowOf427 (Spor .Ru) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  have hcard : Nat.card (Spor .Ru) = 145926144000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  haveI : Finite (Spor .Ru) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ru) := Finite.of_equiv _ b'.symm.toEquiv
  refine rowOf427_of_e9Move ?_ rankTwo_spor_ru
    (fun S _ _ ⟨e⟩ => e9Move_of_ru ⟨e.trans b'.symm⟩) (by rw [hcard]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    ru_orderChecks.1 ru_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem rowOf427_j4
    : RowOf427 (Spor .J4) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.J4.card_J4]
  haveI : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J4) := Finite.of_equiv _ b'.symm.toEquiv
  refine rowOf427_of_e9Move ?_ rankTwo_spor_j4
    (fun S _ _ ⟨e⟩ => e9Move_of_j4 ⟨e.trans b'.symm⟩) (by rw [hcard]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    j4_orderChecks.1 j4_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
