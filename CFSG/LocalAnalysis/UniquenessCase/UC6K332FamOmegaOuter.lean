module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterBound
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterArith
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOdd
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.ClassicalInvolution.Orders.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (OuterRow)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.CatLeafProof (lieOrderDivisor_dvd_numerator)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinate_model_witness_odd coordinate_model_witness_minus coordinateOddWitnessEquiv
    coordinateMinusWitnessEquiv)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (center_matrix_eq_bot)
open CFSG.EvenSmallLie.CatalogOrders (card_eq_lieOrd_of_classical)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
  (outerFixedOrderBoundAt_POmegaOdd outerFixedOrderBoundAt_POmegaMinus)
open CFSG.AGLEmbedding.OuterSylow (lieOrderNumerator_ne_zero)

theorem prod_pow_two_mul_sub_one_dvd (x : ℕ) (s : Finset ℕ) :
    ∏ i ∈ s, (x ^ (2 * i) - 1) ∣ ∏ i ∈ s, ((x ^ 3) ^ (2 * i) - 1) :=
  Finset.prod_dvd_prod_of_dvd _ _ fun i _ => by
    rw [← pow_mul]
    exact Nat.pow_sub_one_dvd_pow_sub_one x (Dvd.intro_left 3 rfl)

theorem three_mul_prod_pow_two_mul_sub_one_dvd {x : ℕ} (hx : ¬ 3 ∣ x) {n : ℕ} (hn : 1 ≤ n) :
    3 * ∏ i ∈ Finset.Icc 1 n, (x ^ (2 * i) - 1) ∣
      ∏ i ∈ Finset.Icc 1 n, ((x ^ 3) ^ (2 * i) - 1) := by
  have hmem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, hn⟩
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem, ← mul_assoc]
  exact mul_dvd_mul (three_mul_sub_one_dvd_cube hx) (prod_pow_two_mul_sub_one_dvd x _)

theorem three_mul_lieOrderNumerator_pomegaOdd_dvd {n : ℕ} (hn : 1 ≤ n) (x : ℕ) :
    3 * lieOrderNumerator .POmegaOdd n x ∣ lieOrderNumerator .POmegaOdd n (x ^ 3) :=
  three_mul_pow_mul_dvd (Nat.one_le_pow _ _ hn) (prod_pow_two_mul_sub_one_dvd x _)
    fun hx => three_mul_prod_pow_two_mul_sub_one_dvd hx hn

theorem three_mul_lieOrderNumerator_pomegaMinus_dvd {n : ℕ} (hn : 2 ≤ n) (x : ℕ) :
    3 * lieOrderNumerator .POmegaMinus n x ∣ lieOrderNumerator .POmegaMinus n (x ^ 3) := by
  have hadd : x ^ n + 1 ∣ (x ^ 3) ^ n + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (x ^ n) 1 (by decide : Odd 3)
    rwa [one_pow, ← pow_mul, mul_comm, pow_mul] at h
  show 3 * (x ^ (n * (n - 1)) * (x ^ n + 1) * _) ∣
    (x ^ 3) ^ (n * (n - 1)) * ((x ^ 3) ^ n + 1) * _
  rw [mul_assoc (x ^ _), mul_assoc ((x ^ 3) ^ _)]
  refine three_mul_pow_mul_dvd (Nat.mul_pos (by omega) (by omega))
    (mul_dvd_mul hadd (prod_pow_two_mul_sub_one_dvd x _)) fun hx => ?_
  rw [mul_left_comm]
  exact mul_dvd_mul hadd (three_mul_prod_pow_two_mul_sub_one_dvd hx (by omega))

theorem outerRow_of_lieModel_pomegaOdd {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (h : LieModel S .POmegaOdd n p f) : OuterRow S := by
  have hcl := h.statedClassicalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcl.2
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_odd hcl K hK e
  have hn : 1 ≤ n := by have := hcl.1.2.2.1; omega
  have hodd : Odd (p ^ f) := (hcl.1.1.eq_two_or_odd'.resolve_left hcl.1.2.2.2).pow
  refine outerRow_of_bound outerFixedOrderBoundAt_POmegaOdd (by decide) (by decide) (by decide)
    hcl.1 h (center_eq_bot_of_mulEquiv (coordinateOddWitnessEquiv K e)
      (center_matrix_eq_bot (by omega) hnd hT)) (show ¬ 3 ∣ 2 by decide) ?_
    (fun x hx => Nat.pos_of_ne_zero (lieOrderNumerator_ne_zero (by decide)
      (Nat.one_le_pow _ _ hn) hx)) (three_mul_lieOrderNumerator_pomegaOdd_dvd hn)
  rw [card_eq_lieOrd_of_classical hcl]
  show ordBC n (p ^ f) * 2 = _
  rw [ordBC, CFSG.ClassicalInvolution.gcd_two_sub_one_of_odd hodd, ← sq]
  exact Nat.div_mul_cancel (lieOrderDivisor_dvd_numerator hcl.1)

theorem outerRow_of_lieModel_pomegaMinus {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (h : LieModel S .POmegaMinus n p f) : OuterRow S := by
  have hcl := h.statedClassicalModel (by decide)
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hcl.2
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hcl K hK b c hirr e
  have hn : 4 ≤ n := hcl.1.2.2
  refine outerRow_of_bound outerFixedOrderBoundAt_POmegaMinus (by decide) (by decide)
    (by decide) hcl.1 h (center_eq_bot_of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c e)
      (center_matrix_eq_bot (by omega) hnd hT)) (fun h3 => by
        have := h3.trans (Nat.gcd_dvd_left 4 _)
        omega) ?_
    (fun x hx => Nat.pos_of_ne_zero (lieOrderNumerator_ne_zero (by decide)
      (Nat.mul_pos (by omega) (by omega)) hx))
    (three_mul_lieOrderNumerator_pomegaMinus_dvd (by omega))
  rw [card_eq_lieOrd_of_classical hcl]
  exact Nat.div_mul_cancel (lieOrderDivisor_dvd_numerator hcl.1)

theorem outerRow_pomegaOdd7 (S : Type) [Group S] [Finite S] (p f : ℕ)
    (h : LieModel S .POmegaOdd 3 p f) (_hp3 : p ≠ 3) : OuterRow S :=
  outerRow_of_lieModel_pomegaOdd h

theorem outerRow_pomegaMinus8 (S : Type) [Group S] [Finite S] (p f : ℕ)
    (h : LieModel S .POmegaMinus 4 p f) (_hp3 : p ≠ 3) : OuterRow S :=
  outerRow_of_lieModel_pomegaMinus h

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
