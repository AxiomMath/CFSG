module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporWords
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import Certificates.Certificate9562

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Item434SporGen

theorem m23_check : m23Check = true :=
  Certificates.certificate9562

theorem rep_m23GenA : Monster.B.Co2.Rep 23 m23GenA CFSG.Sporadic.Schreier.m23PermA := by
  unfold Monster.B.Co2.Rep
  decide

theorem rep_m23GenB : Monster.B.Co2.Rep 23 m23GenB CFSG.Sporadic.Schreier.m23PermB := by
  unfold Monster.B.Co2.Rep
  decide

theorem factorization_card_m23 :
    (Nat.card NativeSporadic.M23).factorization 3 = 2 := by
  rw [CFSG.Sporadic.Schreier.m23_card, show (10200960 : ℕ) = 3 ^ 2 * 1133440 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]

theorem kill9_m23
    (P : Subgroup NativeSporadic.M23) (_hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) : FixGen P ∨ NoSignalizer P := by
  have : Finite NativeSporadic.M23 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num)
  exact Or.inl (fixGen_of_sylow9Check rep_m23GenA rep_m23GenB
    CFSG.Sporadic.Schreier.m23_eq_closure factorization_card_m23 m23_check P hP9)

end Item434SporGen

section Families


theorem item434Spor_M23_9 :
    Item434Spor_M23_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : NativeSporadic.M23 ≃* Spor .M23 := b
  have : Finite NativeSporadic.M23 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num)
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 b' ?_
    (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num) Item434SporGen.kill9_m23
  exact Item434Spor.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.Schreier.at_m23_schreier.1

end Families

end CFSG.RankThree.PartTwo.Sec4
