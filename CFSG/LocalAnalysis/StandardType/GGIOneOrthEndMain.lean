module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrthEnd
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndLift
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEnd
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.AUTSL

section Certs


theorem ggEndNodeIOneNonSmall_orthMinus {K : Type} [Field K] [Finite K] {n m p : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hpn' : ¬ p ∣ n) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGEndNodeIOneNonSmall p m (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hn hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
      norm_num
    exact hodd hpn
  have hn4 : 4 ≤ m + 1 := by omega
  obtain ⟨hnd, -⟩ := regular_coordinateQuadMinus (m + 1) K b c hn4 hbc
  have hΓ : GGEndNodeIOneElt p m (CFSG.RankThree.Classical2.orthDerived (Qm (m + 1) hn4 b c)) :=
    IOneOrthEnd.ggEndNodeIOneElt_orthDerived hK hnd
      (by rw [Module.finrank_fin_fun]; omega) hp hp2
      (OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK hp hpn)
      (by rw [Module.finrank_fin_fun]; omega)
  have hR : GGEndNodeIOneElt p m (OrthRest.RMinus K m b c) :=
    ggEndNodeIOneElt_of_mulEquiv
      ((RecipeFieldOmega.minusEquiv hn4 b c).trans
        (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (Qm (m + 1) hn4 b c))).symm hΓ
  obtain ⟨hZ, hC⟩ := ggOrthRestCenterInput_holds.1 K n m p b c hK (by omega) hp hpn hbc
  exact ggEndNodeIOneNonSmall_of_elt hZ hC
    (fun φ hφ => OrthRest.mem_range_conj_minus (by omega) hbc hK hp hp2 hpn' hφ) hR

theorem ggEndNodeIOne_orthMinus {K : Type} [Field K] [Finite K] {n m p : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hpn' : ¬ p ∣ n) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGEndNodeIOne p m (OrthRest.RMinus K m b c) (LargeEvenInnSet _) :=
  (ggEndNodeIOneNonSmall_orthMinus hK hm hp hpn hpn' hbc).endNodeIOne

theorem ggEndNodeIOne_orthPlus {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2) (hm : 6 ≤ m) :
    GGEndNodeIOne 3 (m - 1) (OrthRest.RPlus K m) (LargeEvenInnSet _) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK'
  obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus m K (by omega)
  have hΓ : GGEndNodeIOneElt 3 (m - 1) (CFSG.RankThree.Classical2.orthDerived
      (coordinateQuadPlus m K)) :=
    IOneOrthEnd.ggEndNodeIOneElt_orthDerived hK' hnd
      (by rw [Module.finrank_fin_fun]; omega) Nat.prime_three (by norm_num)
      (OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK' Nat.prime_three (by norm_num))
      (by rw [Module.finrank_fin_fun]; omega)
  have hR : GGEndNodeIOneElt 3 (m - 1) (OrthRest.RPlus K m) :=
    ggEndNodeIOneElt_of_mulEquiv
      ((RecipeFieldOmega.plusEquiv (K := K) (by omega : 1 ≤ m)).trans
        (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus m K))).symm hΓ
  obtain ⟨hZ, hC⟩ := ggOrthRestCenterInput_holds.2 K m hK (by omega)
  exact ggEndNodeIOne_of_elt hZ hC
    (fun φ hφ => OrthRest.mem_range_conj_plus_two (by omega) hK hφ) hR

theorem ggIOneMoreOrthEndNodeInput_holds : GGIOneMoreOrthEndNodeInput :=
  ⟨fun _ _ _ _ _ _ _ _ hK hm _ hp hpn hpn' hbc => ggEndNodeIOne_orthMinus hK hm hp hpn hpn' hbc,
    fun _ _ _ _ hK hm _ => ggEndNodeIOne_orthPlus hK hm⟩

end Certs

end CFSG.StandardType
