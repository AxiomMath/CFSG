module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporWords
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import Certificates.Certificate9565

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier

namespace Item434SporGen

theorem ru_check : ruCheck = true :=
  Certificates.certificate9565

theorem factorization_card_ruP :
    (Nat.card ruP).factorization 3 = 3 := by
  rw [card_ruP', show (145926144000 : ℕ) = 3 ^ 3 * 5404672000 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]

theorem kill9_ru
    (P : Subgroup ruP) (_hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    FixGen P ∨ NoSignalizer P := by
  have : Finite ruP := Nat.finite_of_card_ne_zero (by rw [card_ruP']; norm_num)
  exact Or.inl (fixGen_of_ex27Check (ga := ruArr4060 0) (gb := ruArr4060 1) rep_ruA0 rep_ruA1
    rfl factorization_card_ruP ru_check P hP9)

end Item434SporGen

section Families


theorem item434Spor_Ru_9 :
    Item434Spor_Ru_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have bP : ruP ≃* Spor .Ru := ruEquivP.symm.trans b
  have : Finite ruP := Nat.finite_of_card_ne_zero (by rw [card_ruP']; norm_num)
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 bP ?_ (by rw [card_ruP']; norm_num)
    Item434SporGen.kill9_ru
  rw [card_outer_ruP]
  norm_num

end Families

end CFSG.RankThree.PartTwo.Sec4
