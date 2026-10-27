module

import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec18.Item183KSL
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem isSLThreePi_of_SL34 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (e : K ⧸ CFSG.pCore 2 K ≃* Item183K.SL34) :
    Sec4.IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K) := by
  have hk := KFacts.L34.card_galoisField_two_two
  have : Finite (GaloisField 2 2) := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  exact ⟨4, GaloisField 2 2, inferInstance, inferInstance, Or.inl ⟨hk, by norm_num,
    ⟨(QuotientGroup.quotientMulEquivOfEq
      (Item183K.aschbacherSolvableCore_eq_pCore_of_SL34 e)).trans
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _))⟩⟩⟩

end CFSG.RankThree.PartTwo.Sec18
