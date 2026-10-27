module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTrans
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEnd

public section

namespace CFSG.StandardType

namespace SmallOrth

open CFSG.Assembly TableB TableBOrth SmallOrthUn

theorem plusTwoVacuousInput_holds : PlusTwoVacuousInput := by
  intro K _ _ m hK hm A D a hE hr hU
  haveI : CharP K 2 := charP_two_of_card (n := 1) le_rfl (by rw [hK, pow_one])
  have hK1 : ∀ c : K, c ^ 3 = 1 → c = 1 :=
    OrthRestOdd.eq_one_of_pow_eq_one_of_dvd (n := 1) (p := 3) (by rw [hK, pow_one])
      Nat.prime_three (by norm_num)
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  set ψ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K with hψ
  have hΩ : (LargeEvenOmega (LargeEvenQPlus K m)).map ψ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (qPlusForm K m) := by
    rw [← coe_qPlusForm (K := K) m]
    exact map_largeEvenOmega (qPlusForm K m)
  have hfin : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hE' := endData_mapEquiv ψ hΩ hE
  have hcard : Nat.card (A.map ψ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ψ.injective
  exact bigConcl_of_mapEquiv ψ (bigConcl_of_normalizes (nondegenerate_qPlusForm (K := K) m)
    Nat.prime_three (by norm_num) hK1 hpq hfin (by omega) hE' (hcard ▸ hr)
    (normalizesTwoGroup_mapEquiv ψ hΩ hU))

theorem minusUnitVacuousInput_holds : MinusUnitVacuousInput := by
  intro K _ _ n m p b c hK hm hp hpn hirr A D a hE hr hU
  haveI : CharP K 2 := charP_two_of_card (one_le_of_card hK) hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by have := one_le_of_card hK; omega))]
      norm_num
    exact hodd hpn
  have hK1 : ∀ x : K, x ^ p = 1 → x = 1 := OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK hp hpn
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  set ψ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K with hψ
  have hΩ : (LargeEvenOmega (LargeEvenQMinus m b c)).map ψ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (qMinusForm K m b c) := by
    rw [← coe_qMinusForm (K := K) m b c]
    exact map_largeEvenOmega (qMinusForm K m b c)
  have hfin : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    ring
  have hE' := endData_mapEquiv ψ hΩ hE
  have hcard : Nat.card (A.map ψ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ψ.injective
  exact bigConcl_of_mapEquiv ψ (bigConcl_of_normalizes (nondegenerate_qMinusForm m hirr) hp hp2
    hK1 hpq hfin (by omega) hE' (by rw [hcard]; simpa using hr)
    (normalizesTwoGroup_mapEquiv ψ hΩ hU))

end SmallOrth

end CFSG.StandardType

end
