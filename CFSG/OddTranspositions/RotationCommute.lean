module

public import CFSG.Timmesfeld.Bridge.OddTranspSecondKind

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem rotation_not_commute_uv (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v a : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (ha : a ∈ Subgroup.zpowers (u * w)) (ha1 : a ≠ 1) :
    ¬ Commute a (u * v) := by
  intro hcomm
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  have hw2 : w * w = 1 := hD.mul_self_eq_one htri.2.2.1
  have hodd_uw : Odd (orderOf (u * w)) :=
    hD.odd_of_not_commute htri.1 htri.2.2.1 htri.2.2.2.2.2.1
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hrD : u * (u * w) ^ j ∈ D := by
    rw [mul_zpow_mul_eq_zpow_neg_mul hu2 hw2 j]
    obtain ⟨k, hk⟩ := exists_zpow_conj_eq hu2 hw2 hodd_uw (-j)
    rw [← hk]
    exact hN _ u htri.1
  have hvne : v ≠ u * (u * w) ^ j := by
    intro hveq
    have huv : u * v = (u * w) ^ j := by
      calc u * v = u * (u * (u * w) ^ j) := by rw [hveq]
        _ = (u * w) ^ j := by rw [← mul_assoc, hu2, one_mul]
    have h2 : orderOf (u * v) = 2 :=
      hD.orderOf_mul_eq_two htri.1 htri.2.1 htri.2.2.2.1 htri.2.2.2.2.1
    have hodd : Odd (orderOf ((u * w) ^ j)) := odd_orderOf_zpow hodd_uw j
    rw [← huv, h2] at hodd
    exact absurd hodd (by decide)
  have hodd_a : Odd (orderOf ((u * w) ^ j)) := odd_orderOf_zpow hodd_uw j
  have hcop : Nat.Coprime (orderOf (u * v)) (orderOf ((u * w) ^ j)) := by
    rw [hD.orderOf_mul_eq_two htri.1 htri.2.1 htri.2.2.2.1 htri.2.2.2.2.1]
    exact Nat.coprime_two_left.mpr hodd_a
  have hord : orderOf ((u * v) * (u * w) ^ j) = 2 * orderOf ((u * w) ^ j) := by
    rw [hcomm.symm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
      hD.orderOf_mul_eq_two htri.1 htri.2.1 htri.2.2.2.1 htri.2.2.2.2.1]
  have ha_gt : 1 < orderOf ((u * w) ^ j) := by
    have hne : orderOf ((u * w) ^ j) ≠ 1 := fun h1 => ha1 (orderOf_eq_one_iff.mp h1)
    have hpos := hodd_a.pos
    omega
  have hvr : v * (u * (u * w) ^ j) = (u * v) * (u * w) ^ j := by
    rw [← mul_assoc, ← htri.2.2.2.2.1.eq]
  rcases hD.2 v htri.2.1 (u * (u * w) ^ j) hrD with hdvd | hodd
  · rw [hvr, hord] at hdvd
    have hle : 2 * orderOf ((u * w) ^ j) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · rw [hvr, hord] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega

end CFSG.OddTranspositions
