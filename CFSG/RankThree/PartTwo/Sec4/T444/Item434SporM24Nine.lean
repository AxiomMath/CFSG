module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporWords
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import Certificates.Certificate9563

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Item434SporGen

theorem m24_check : m24Check = true :=
  Certificates.certificate9563

theorem rep_m24GenA : Monster.B.Co2.Rep 24 m24GenA CFSG.Sporadic.Mathieu.m24gA := by
  unfold Monster.B.Co2.Rep
  decide

theorem rep_m24GenB : Monster.B.Co2.Rep 24 m24GenB CFSG.Sporadic.Mathieu.m24gB := by
  unfold Monster.B.Co2.Rep
  decide

theorem factorization_card_m24 :
    (Nat.card NativeSporadic.M24).factorization 3 = 3 := by
  rw [CFSG.Sporadic.Mathieu.card_M24, show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]

theorem kill9_m24
    (P : Subgroup NativeSporadic.M24) (_hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) : FixGen P ∨ NoSignalizer P := by
  have : Finite NativeSporadic.M24 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
  exact Or.inl (fixGen_of_ex27Check rep_m24GenA rep_m24GenB CFSG.Sporadic.Mathieu.m24_eq
    factorization_card_m24 m24_check P hP9)

end Item434SporGen

section Families


theorem item434Spor_M24_9 :
    Item434Spor_M24_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : NativeSporadic.M24 ≃* Spor .M24 := b
  have : Finite NativeSporadic.M24 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 b' ?_
    (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num) Item434SporGen.kill9_m24
  exact Item434Spor.not_three_dvd_card_outer_of_le_two
    (Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
      (CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))))

end Families

end CFSG.RankThree.PartTwo.Sec4
