module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4FieldFix
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)
open CFSG.Assembly.RankThreeEven (projSU)

theorem card_projSU_four_two_eq {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (projSU 4 2 m) =
      (2 ^ m) ^ 6 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)) := by
  rw [← Nat.card_congr (Res417Six.unitarySUEquivProjSU hm).toEquiv]
  exact Item419Res3.card_unitarySU_four (unitaryFieldData_galoisField 2 m hm)

theorem three_dvd_pow_four_add_sq_add_one (k : ℕ) : 3 ∣ (2 ^ k) ^ 4 + (2 ^ k) ^ 2 + 1 := by
  have h2 : (2 ^ k) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  have h4 : (2 ^ k) ^ 4 % 3 = 1 := by
    rw [show (2 ^ k) ^ 4 = ((2 ^ k) ^ 2) ^ 2 by ring, Nat.pow_mod, h2]
  omega

theorem three_mul_card_dvd_cube (k : ℕ) :
    3 * ((2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1))) ∣
      (2 ^ (3 * k)) ^ 6 * (((2 ^ (3 * k)) ^ 2 - 1) * ((2 ^ (3 * k)) ^ 3 + 1) *
        ((2 ^ (3 * k)) ^ 4 - 1)) := by
  obtain ⟨t, ht⟩ := three_dvd_pow_four_add_sq_add_one k
  have ha : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_mul']
  generalize 2 ^ k = a at ha ht ⊢
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have h4 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ ha
  have h6 : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ ha)
  have h12 : 1 ≤ (a ^ 3) ^ 4 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ ha)
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub h2, Nat.cast_sub h4, Nat.cast_sub h6, Nat.cast_sub h12]
  refine ⟨(a : ℤ) ^ 12 * t * ((a : ℤ) ^ 6 - (a : ℤ) ^ 3 + 1) * ((a : ℤ) ^ 8 + (a : ℤ) ^ 4 + 1),
    ?_⟩
  have ht' : (a : ℤ) ^ 4 + (a : ℤ) ^ 2 + 1 = 3 * (t : ℤ) := by exact_mod_cast ht
  linear_combination ((a : ℤ) ^ 18 * (((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 3 + 1) * ((a : ℤ) ^ 4 - 1)) *
    ((a : ℤ) ^ 6 - (a : ℤ) ^ 3 + 1) * ((a : ℤ) ^ 8 + (a : ℤ) ^ 4 + 1)) * ht'

theorem center_projSU_four_two_eq_bot {m : ℕ} (hm : 1 ≤ m) :
    Subgroup.center (projSU 4 2 m) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (projSU 4 2 m) :=
    CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
      ⟨Nat.prime_two, hm, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (projSU 4 2 m)) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative (projSU 4 2 m) := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center (projSU 4 2 m) := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    have hp : (Nat.card (projSU 4 2 m)).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [card_projSU_four_two_eq hm] at hp
    have hd2 : 2 ∣ (2 ^ m) ^ 6 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)) :=
      Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _
    have hd3 : 3 ∣ (2 ^ m) ^ 6 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1)) := by
      refine Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) _
      have h4 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4]
      simpa using Nat.sub_one_dvd_pow_sub_one 4 m
    have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd2
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd3
    omega

theorem outerRow_projSU_four_two_all {m : ℕ} (hm : 1 ≤ m) : OuterRow (projSU 4 2 m) := by
  refine outerRow_of_fixed_card_dvd (center_projSU_four_two_eq_bot hm) fun σ hσ hout => ?_
  obtain ⟨k, hk, -, hcard⟩ := exists_card_fixSub_projSU_four_two hm hσ hout
  refine ⟨Item426.fixSub σ, _, fun x => Item426.mem_fixSub, hcard.dvd, ?_⟩
  rw [card_projSU_four_two_eq hm, hk]
  exact three_mul_card_dvd_cube k

end CFSG.RankThree.PartTwo.Sec4.RonanK432
