module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.O4CloseReduction
import CFSG.OddTranspositions.PartThree.EightSix.OFourMinusCheck
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import Certificates.Certificate1430001
public import CFSG.OddTranspositions.SixEight
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Timmesfeld.Bridge.Asc72

private theorem orderOf_mul_eq_of_map {X : Type} [Group X] {φ : X ≃* minusPerm} {x y : X}
    {i j : Fin 65} (hx : ((φ x : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl i)
    (hy : ((φ y : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl j) :
    orderOf (x * y) = orderOf (minusRefl i * minusRefl j) := by
  calc orderOf (x * y) = orderOf (φ (x * y)) := (φ.orderOf_eq (x * y)).symm
    _ = orderOf (φ x * φ y) := by rw [map_mul]
    _ = orderOf (((φ x * φ y : minusPerm) : Equiv.Perm (Fin 65))) :=
      (Subgroup.orderOf_coe (φ x * φ y)).symm
    _ = orderOf (minusRefl i * minusRefl j) := by rw [Subgroup.coe_mul, hx, hy]

private theorem commute_minusRefl_of_commute {X : Type} [Group X] {φ : X ≃* minusPerm}
    {x y : X} {i j : Fin 65}
    (hx : ((φ x : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl i)
    (hy : ((φ y : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl j)
    (hxy : Commute x y) : Commute (minusRefl i) (minusRefl j) := by
  have hcoe : Commute ((φ x : minusPerm) : Equiv.Perm (Fin 65))
      ((φ y : minusPerm) : Equiv.Perm (Fin 65)) :=
    (hxy.map φ).map (Subgroup.subtype minusPerm)
  simpa [hx, hy] using hcoe

private theorem not_commute_minusRefl_of_not_commute {X : Type} [Group X]
    {φ : X ≃* minusPerm} {x y : X} {i j : Fin 65}
    (hx : ((φ x : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl i)
    (hy : ((φ y : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl j)
    (hxy : ¬ Commute x y) : ¬ Commute (minusRefl i) (minusRefl j) := by
  intro hc
  apply hxy
  have hcoe : Commute ((φ x : minusPerm) : Equiv.Perm (Fin 65))
      ((φ y : minusPerm) : Equiv.Perm (Fin 65)) := by
    simpa [hx, hy] using hc
  exact Commute.of_map φ.injective
    (Commute.of_map (Subgroup.subtype_injective minusPerm) hcoe)


private theorem rep_minusTable (i : Fin 65) :
    Rep 65 minusTable[(i : ℕ)]! (minusRefl i) :=
  fun x => (minusRefl_apply i x).symm

private theorem rep_minusTripleArr (i k j : Fin 65) :
    Rep 65 (minusTripleArr (i : ℕ) (k : ℕ) (j : ℕ))
      (minusRefl i * minusRefl k * minusRefl j) := by
  unfold minusTripleArr
  exact rep_compA (rep_compA (rep_minusTable i) (rep_minusTable k)) (rep_minusTable j)

private theorem rep_minusTripleSq (i k j : Fin 65) :
    Rep 65 (minusTripleSq (i : ℕ) (k : ℕ) (j : ℕ))
      ((minusRefl i * minusRefl k * minusRefl j) *
        (minusRefl i * minusRefl k * minusRefl j)) := by
  unfold minusTripleSq
  exact rep_compA (rep_minusTripleArr i k j) (rep_minusTripleArr i k j)

private theorem rep_minusTripleFourth (i k j : Fin 65) :
    Rep 65 (minusTripleFourth (i : ℕ) (k : ℕ) (j : ℕ))
      (((minusRefl i * minusRefl k * minusRefl j) *
          (minusRefl i * minusRefl k * minusRefl j)) *
        ((minusRefl i * minusRefl k * minusRefl j) *
          (minusRefl i * minusRefl k * minusRefl j))) := by
  unfold minusTripleFourth
  exact rep_compA (rep_minusTripleSq i k j) (rep_minusTripleSq i k j)

private theorem rep_minusPairArr (i j : Fin 65) :
    Rep 65 (minusPairArr (i : ℕ) (j : ℕ)) (minusRefl i * minusRefl j) := by
  unfold minusPairArr
  exact rep_compA (rep_minusTable i) (rep_minusTable j)

private theorem rep_minusPairCube (i j : Fin 65) :
    Rep 65 (minusPairCube (i : ℕ) (j : ℕ))
      ((minusRefl i * minusRefl j) * (minusRefl i * minusRefl j) *
        (minusRefl i * minusRefl j)) := by
  unfold minusPairCube
  exact rep_compA (rep_compA (rep_minusPairArr i j) (rep_minusPairArr i j))
    (rep_minusPairArr i j)

private theorem minusTable_beq_commute_iff (i j : Fin 65) :
    (((minusTable[(i : ℕ)]!)[(j : ℕ)]! == (j : ℕ)) = true) ↔
      Commute (minusRefl i) (minusRefl j) := by
  rw [beq_iff_eq, commute_minusRefl_iff]
  exact ⟨fun h => Fin.ext ((minusRefl_apply i j).trans h),
    fun h => (minusRefl_apply i j).symm.trans
      (congrArg (fun x : Fin 65 => (x : ℕ)) h)⟩

private theorem orderOf_minusRefl_mul_eq_three_of_cube {i j : Fin 65}
    (hij : ¬ Commute (minusRefl i) (minusRefl j))
    (h3 : eqA 65 (minusPairCube (i : ℕ) (j : ℕ)) (idA 65) = true) :
    orderOf (minusRefl i * minusRefl j) = 3 := by
  have hcube : (minusRefl i * minusRefl j) ^ 3 = 1 := by
    have h := (eqA_iff (rep_minusPairCube i j) rep_idA).1 h3
    rw [pow_three']
    exact h
  have hne : minusRefl i * minusRefl j ≠ 1 := by
    intro h
    apply hij
    have hri : minusRefl i = minusRefl j := by
      have h' : minusRefl j = (minusRefl i)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h', inv_eq_of_mul_eq_one_right (minusRefl_mul_self i)]
    rw [hri]
  exact orderOf_eq_prime (hp := ⟨by norm_num⟩) hcube hne

private theorem minusSecondKindCheck_condition {i j k : Fin 65}
    (h4 : orderOf (minusRefl i * minusRefl k * minusRefl j) = 4) :
    (eqA 65 (minusTripleFourth (i : ℕ) (k : ℕ) (j : ℕ)) (idA 65) &&
      !eqA 65 (minusTripleSq (i : ℕ) (k : ℕ) (j : ℕ)) (idA 65)) = true := by
  have hg4 : (minusRefl i * minusRefl k * minusRefl j) ^ 4 = 1 := by
    rw [← h4]
    exact pow_orderOf_eq_one _
  have h4arr : eqA 65 (minusTripleFourth (i : ℕ) (k : ℕ) (j : ℕ)) (idA 65) = true := by
    rw [eqA_iff (rep_minusTripleFourth i k j) rep_idA]
    calc
      ((minusRefl i * minusRefl k * minusRefl j) *
            (minusRefl i * minusRefl k * minusRefl j)) *
          ((minusRefl i * minusRefl k * minusRefl j) *
            (minusRefl i * minusRefl k * minusRefl j))
          = (minusRefl i * minusRefl k * minusRefl j) ^ 2 *
            (minusRefl i * minusRefl k * minusRefl j) ^ 2 := by rw [pow_two]
      _ = (minusRefl i * minusRefl k * minusRefl j) ^ (2 + 2) :=
        (pow_add _ 2 2).symm
      _ = (minusRefl i * minusRefl k * minusRefl j) ^ 4 := by norm_num
      _ = 1 := hg4
  have h2ne : (minusRefl i * minusRefl k * minusRefl j) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (n := 2) (by norm_num) (by rw [h4]; norm_num)
  have h2arr : eqA 65 (minusTripleSq (i : ℕ) (k : ℕ) (j : ℕ)) (idA 65) = false := by
    rw [Bool.eq_false_iff]
    intro h
    apply h2ne
    have h' := (eqA_iff (rep_minusTripleSq i k j) rep_idA).1 h
    rw [pow_two]
    exact h'
  exact Bool.and_eq_true_iff.mpr ⟨h4arr, by simpa using h2arr⟩

theorem orderOf_minusRefl_mul_eq_three {i j k : Fin 65} (hik : i ≠ k)
    (hc : Commute (minusRefl i) (minusRefl k)) (hij : ¬ Commute (minusRefl i) (minusRefl j))
    (hkj : ¬ Commute (minusRefl k) (minusRefl j))
    (h4 : orderOf (minusRefl i * minusRefl k * minusRefl j) = 4) :
    orderOf (minusRefl i * minusRefl j) = 3 ∧ orderOf (minusRefl k * minusRefl j) = 3 := by
  have hspec := allLt_spec (allLt_spec (allLt_spec
    (show minusSecondKindCheck () = true from Certificates.certificate1430001)
    (i := (i : ℕ)) i.isLt) (i := (k : ℕ)) k.isLt) (i := (j : ℕ)) j.isLt
  have hik' : ((i : ℕ) == (k : ℕ)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hik (Fin.ext h)
  have hck' := (minusTable_beq_commute_iff i k).2 hc
  have hij' : ((minusTable[(i : ℕ)]!)[(j : ℕ)]! == (j : ℕ)) = false :=
    Bool.eq_false_iff.mpr fun h => hij ((minusTable_beq_commute_iff i j).1 h)
  have hkj' : ((minusTable[(k : ℕ)]!)[(j : ℕ)]! == (j : ℕ)) = false :=
    Bool.eq_false_iff.mpr fun h => hkj ((minusTable_beq_commute_iff k j).1 h)
  have hcond := minusSecondKindCheck_condition (i := i) (k := k) (j := j) h4
  simp only [hik', hck', hij', hkj', hcond, if_true, if_false, Bool.false_eq_true] at hspec
  obtain ⟨h3i, h3k⟩ := Bool.and_eq_true_iff.mp hspec
  exact ⟨orderOf_minusRefl_mul_eq_three_of_cube hij h3i,
    orderOf_minusRefl_mul_eq_three_of_cube hkj h3k⟩


theorem orderOf_mul_eq_three_of_o4PairData {X : Type} [Group X] {Θ : Set X}
    (hO : CFSG.OddTranspositions.QZ.O4PairData X Θ) {u w v : X} (htri : IsTriangle Θ u w v)
    (h4 : orderOf (u * v * w) = 4) : orderOf (u * w) = 3 ∧ orderOf (v * w) = 3 := by
  obtain ⟨e, he⟩ := hO
  obtain ⟨e', he'⟩ := isO4Minus5Pair_minusPerm
  let φ : X ≃* minusPerm := e.trans e'.symm
  have hφΘ : φ '' Θ = minusClass := by
    rw [MulEquiv.coe_trans, Set.image_comp, he]
    rw [← he', ← Set.image_comp]
    simp
  have hclass : ∀ x ∈ Θ, ∃ i, ((φ x : minusPerm) : Equiv.Perm (Fin 65)) = minusRefl i := by
    intro x hx
    have hx' : φ x ∈ minusClass := by
      rw [← hφΘ]
      exact ⟨x, hx, rfl⟩
    simpa [minusClass] using hx'
  obtain ⟨i, hi⟩ := hclass u htri.1
  obtain ⟨k, hk⟩ := hclass v htri.2.1
  obtain ⟨j, hj⟩ := hclass w htri.2.2.1
  have hik : i ≠ k := by
    rintro rfl
    exact htri.2.2.2.1 (φ.injective (Subtype.ext (hi.trans hk.symm)))
  have hc := commute_minusRefl_of_commute hi hk htri.2.2.2.2.1
  have hij := not_commute_minusRefl_of_not_commute hi hj htri.2.2.2.2.2.1
  have hkj := not_commute_minusRefl_of_not_commute hk hj htri.2.2.2.2.2.2
  have h4' : orderOf (minusRefl i * minusRefl k * minusRefl j) = 4 := by
    have hcoe : (((φ u * φ v * φ w : minusPerm) : Equiv.Perm (Fin 65)))
        = minusRefl i * minusRefl k * minusRefl j := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hi, hk, hj]
    have hmap : φ u * φ v * φ w = φ (u * v * w) := by rw [map_mul, map_mul]
    rw [← hcoe, Subgroup.orderOf_coe, hmap, φ.orderOf_eq, h4]
  have h3 := orderOf_minusRefl_mul_eq_three hik hc hij hkj h4'
  exact ⟨(orderOf_mul_eq_of_map hi hj).trans h3.1, (orderOf_mul_eq_of_map hk hj).trans h3.2⟩

end CFSG.OddTranspositions.PartThree.EightSix
