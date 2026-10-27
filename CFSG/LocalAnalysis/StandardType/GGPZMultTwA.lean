module

public import CFSG.LocalAnalysis.StandardType.GGPZMultCore
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LieType.Steinberg.CentralExt.GriessClassical
import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.LieType.Multipliers.U62Sylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

private theorem pzmt_not_dvd_generic {p l n : ℕ} (hpl : ¬ p ∣ l + 1) :
    ¬ p ∣ (genericOrders .PSU (l + 1) 2 n).1 * (genericOrders .PSU (l + 1) 2 n).2 := by
  rw [show genericOrders .PSU (l + 1) 2 n = (Nat.gcd (l + 1) (2 ^ n + 1), 1) from rfl]
  simp only [Prod.fst, Prod.snd, mul_one]
  intro h
  exact hpl (h.trans (Nat.gcd_dvd_left _ _))

private theorem pzmt_pow_two_eq_two {n : ℕ} (hn : 1 ≤ n) (h : 2 ^ n = 2) : n = 1 := by
  have h2 : ¬ 2 ≤ n := by
    intro h2
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  omega

theorem ggPZMult_twA
    {Y : Type} [Group Y] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hΛ : LargeEvenInLambda2 ⟨.twA, l, n⟩) (hperf : commutator Y = ⊤)
    (hlab : GGHasLabel ⟨.twA, l, n⟩ (Y ⧸ Subgroup.center Y))
    (hpq : p ∣ 2 ^ n + 1) (hpl : ¬ p ∣ l + 1) : ¬ p ∣ Nat.card (Subgroup.center Y) := by
  have hl2 : 2 ≤ l := hΛ.2.1
  have hnpos : 1 ≤ n := hΛ.1
  unfold GGHasLabel at hlab
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeUnitary at hlab
  obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have hne : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hΛ.2.2 hl
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hadm : CFSG.Open.StatedLieAdmissible .PSU (l + 1) 2 n :=
    ⟨Nat.prime_two, hΛ.1, by omega, hne⟩
  have hmod : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) .PSU (l + 1) 2 n :=
    statedClassicalModel_unitary (l + 1) n hKcard hadm
  have hmod' : CFSG.Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU (l + 1) 2 n :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmod
  have hmult : Nonempty (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y) ≃*
      generic .PSU (l + 1) 2 n × exceptional .PSU (l + 1) 2 n) := by
    by_cases he : Even (l + 1)
    · by_cases hq : 4 ≤ 2 ^ n ∨ (2 ^ n = 2 ∧ 8 ≤ l + 1) ∨ (2 ^ n = 3 ∧ 6 ≤ l + 1)
      · exact (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row hmod' he hq).2
      · have hlt4 : 2 ^ n < 4 := by
          by_contra hge
          exact hq (Or.inl (not_lt.mp hge))
        have hge2 : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnpos
        have hne3 : 2 ^ n ≠ 3 := by
          intro h3
          have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
          rw [h3] at hdvd
          norm_num at hdvd
        have hpow2 : 2 ^ n = 2 := by omega
        have hn1 : n = 1 := pzmt_pow_two_eq_two hnpos hpow2
        have hnot8 : ¬ 8 ≤ l + 1 := by
          intro h8
          exact hq (Or.inr (Or.inl ⟨hpow2, h8⟩))
        have hl46 : l + 1 = 4 ∨ l + 1 = 6 := by
          obtain ⟨k, hk⟩ := he
          omega
        rcases hl46 with hl4 | hl6
        · obtain rfl : l = 3 := by omega
          obtain rfl : n = 1 := hn1
          exact (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_four_two_row
            (CFSG.LieType.Steinberg.CentralExt.GriessNative.models_lieModel_of_classical
              hmod')).2
        · obtain rfl : l = 5 := by omega
          obtain rfl : n = 1 := hn1
          exfalso
          have hp3 : p ∣ 3 := by simpa using hpq
          have hpe : p = 3 :=
            (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hp3
          exact hpl (hpe ▸ (by norm_num : 3 ∣ 5 + 1))
    · exact (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hmod' he).2
  exact ggPZMult_not_dvd_of_row hperf (Fact.out : p.Prime) hp2 hmult
    (pzmt_not_dvd_generic hpl)

end CFSG.StandardType

end
