module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowGen
import CFSG.HardMathSupport.Curtis.Proving.NineDvdCentralizer
import CFSG.RankThree.PartTwo.KFacts.KP4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Asc83Table.M22

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

theorem l143Rows_M22 :
    L143Rows CFSG.Blueprint.NativeSporadic.M22 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.M22).factorization 3 = 2 :=
    CFSG.RankThree.Asc83Table.M22.factorization_card
  intro x hx3 hx1
  refine L143Row.of_nine_dvd hx3
    (CFSG.HardMathSupport.Curtis.Proving.nine_dvd_card_centralizer_of_orderOf_eq_three
      (by rw [hcard]; norm_num) (orderOf_eq_prime hx3 hx1)) ?_
  rintro y ⟨k, hk⟩
  have hp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hP9 : Nat.card (P : Subgroup CFSG.Blueprint.NativeSporadic.M22) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hy3 : y ^ 3 = 1 :=
    (CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.mp
      (CFSG.RankThree.PartTwo.KFacts.KP4.m22_isElementaryAbelian ⟨MulEquiv.refl _⟩ hP9)).2 y
      (hP (Subgroup.mem_zpowers y))
  refine ⟨hy3, ?_⟩
  by_cases hy1 : y = 1
  · exact ⟨1, by rw [hy1]; simp⟩
  have ho : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have ho' : orderOf y⁻¹ = 3 := by rw [orderOf_inv, ho]
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.RankThree.PartTwo.KFacts.KP4.m22_isConj_of_orderOf ⟨MulEquiv.refl _⟩ ho ho')
  exact ⟨c, hc⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
