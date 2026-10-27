module

public import CFSG.Quasithin.Vol2.Ch11SecA02Arith
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Quasithin.Vol2.Ch11SecAKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp StatedProj StatedScalars)

variable {K : Type} [Field K] [Finite K]

theorem card_SL_two {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ m * oSL2 m := by
  rw [OrderReductions.LinearOrders.card_specialLinear K 2 (by norm_num), hK]
  have hI : Finset.Icc 2 2 = {2} := by decide
  rw [hI, Finset.prod_singleton, oSL2, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, ← pow_mul,
    mul_comm m 2]

theorem card_SL_three' {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 2 ^ (3 * n) * oSL3 n := by
  rw [CFSG.BrauerLinearThree.card_SL_three, hK, oSL3, ← pow_mul, ← pow_mul,
    mul_comm n 3, mul_comm n 2, mul_assoc]

omit [Finite K] in
theorem card_center_SL_three_le :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  have := card_rootsOfUnity (R := K) (Fintype.card (Fin 3))
  simpa using this

theorem card_PSL_three :
    ∃ c : ℕ, (c = 1 ∨ c = 3) ∧
      c * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
  have hq := (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 3) K)).card_eq_card_quotient_mul_card_subgroup
  refine ⟨Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)), ?_, ?_⟩
  · rw [OrderReductions.LinearOrders.card_specialLinear_center K 3 (by norm_num)]
    have h3 : Nat.gcd 3 (Nat.card K - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    have hle : Nat.gcd 3 (Nat.card K - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    have hpos : 0 < Nat.gcd 3 (Nat.card K - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    interval_cases h : Nat.gcd 3 (Nat.card K - 1)
    · exact Or.inl rfl
    · exact absurd h3 (by norm_num)
    · exact Or.inr rfl
  · rw [hq, mul_comm]

theorem card_PSL_two {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num),
    ← OrderReductions.LinearOrders.card_specialLinear K 2 (by norm_num)]
  have h1 : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    rw [hK]
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · have := Finite.one_lt_card (α := K)
        rw [hK] at this
        norm_num at this
      · exact h
    exact Nat.coprime_two_left.mpr (odd_two_pow_sub_one hm)
  rw [h1, Nat.div_one]

theorem card_Sp_four {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSp 2 K) = 2 ^ (4 * n) * oSp4 n := by
  rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num), hK, oSp4, ← pow_mul, ← pow_mul, ← pow_mul]
  ring_nf

theorem card_range_dvd {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B) :
    Nat.card f.range ∣ Nat.card A := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem card_scalars_subgroupOf_dvd {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι K)) :
    Nat.card ((StatedScalars ι K).subgroupOf H) ∣ Nat.card K - 1 := by
  have h1 : Nat.card ((StatedScalars ι K).subgroupOf H) ∣ Nat.card (StatedScalars ι K) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (StatedScalars ι K) ∣ Nat.card Kˣ :=
    card_range_dvd (Matrix.GeneralLinearGroup.scalar ι)
  rw [Nat.card_units] at h2
  exact h1.trans h2

end CFSG.Quasithin.Vol2.Ch11.SecA
