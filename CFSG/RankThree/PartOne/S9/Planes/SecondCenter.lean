module

public import CFSG.RankThree.PartOne.S9.StatementsAlpha
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.Planes.NormalPlane

public section

namespace CFSG.RankThree.PartOne.Planes

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem pow_mul_mul_inv_pow_of_commute {x y : P} (hc : Commute ⁅x, y⁆ x) :
    ∀ n : ℕ, x ^ n * y * (x ^ n)⁻¹ = ⁅x, y⁆ ^ n * y
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_mul_inv_pow_of_commute hc n
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * (⁅x, y⁆ ^ n * y) * x⁻¹ := by rw [ih]
      _ = ⁅x, y⁆ ^ n * (x * y * x⁻¹) := by
          rw [show x * (⁅x, y⁆ ^ n * y) * x⁻¹ = (x * ⁅x, y⁆ ^ n) * y * x⁻¹ by group,
            ((hc.pow_left n).eq).symm]
          group
      _ = ⁅x, y⁆ ^ (n + 1) * y := by rw [hxy, pow_succ, mul_assoc]

theorem commutatorElement_pow_left {x y : P} (hc : Commute ⁅x, y⁆ x) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  rw [commutatorElement_def, pow_mul_mul_inv_pow_of_commute hc n, mul_inv_cancel_right]

theorem mul_pow_of_commute_commutator {x y : P} (hx : Commute ⁅y, x⁆ x)
    (hy : Commute ⁅y, x⁆ y) : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)
  | 0 => by simp
  | n + 1 => by
    have ih := mul_pow_of_commute_commutator hx hy n
    set c := ⁅y, x⁆ with hc
    have hyn : y ^ n * x = c ^ n * x * y ^ n := by
      have h := pow_mul_mul_inv_pow_of_commute (x := y) (y := x) hy n
      calc y ^ n * x = (y ^ n * x * (y ^ n)⁻¹) * y ^ n := by group
        _ = c ^ n * x * y ^ n := by rw [h]
    have hcC : Commute (c ^ (n.choose 2)) (x * y) := (hx.pow_left _).mul_right (hy.pow_left _)
    have h1 : Commute (c ^ n) (x ^ (n + 1)) := (hx.pow_left _).pow_right _
    have h2 : Commute (c ^ n) (y ^ (n + 1)) := (hy.pow_left _).pow_right _
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = x ^ n * y ^ n * c ^ (n.choose 2) * (x * y) := by rw [pow_succ, ih]
      _ = x ^ n * (y ^ n * x) * y * c ^ (n.choose 2) := by
          rw [mul_assoc (x ^ n * y ^ n), hcC.eq]; group
      _ = c ^ n * x ^ (n + 1) * y ^ (n + 1) * c ^ (n.choose 2) := by
          rw [hyn, pow_succ, pow_succ]
          have h0 : Commute (c ^ n) (x ^ n) := (hx.pow_left _).pow_right _
          calc x ^ n * (c ^ n * x * y ^ n) * y * c ^ n.choose 2
              = (x ^ n * c ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by group
            _ = (c ^ n * x ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by rw [h0.eq]
            _ = c ^ n * (x ^ n * x) * (y ^ n * y) * c ^ n.choose 2 := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1).choose 2) := by
          rw [h1.eq, mul_assoc (x ^ (n + 1)), h2.eq, hch, pow_add]
          group

theorem mem_upperCentralSeries_two_iff {x : P} :
    x ∈ Subgroup.upperCentralSeries P 2 ↔ ∀ y : P, ⁅x, y⁆ ∈ center P := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
    Subgroup.upperCentralSeries_one]

@[expose] def torsionSecondCenter (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Subgroup P where
  carrier := {x | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1}
  mul_mem' := by
    rintro x y ⟨hxZ, hxp⟩ ⟨hyZ, hyp⟩
    refine ⟨mul_mem hxZ hyZ, ?_⟩
    have hc : ⁅y, x⁆ ∈ center P := mem_upperCentralSeries_two_iff.1 hyZ x
    have hcx : Commute ⁅y, x⁆ x := (mem_center_iff.1 hc x).symm
    have hcy : Commute ⁅y, x⁆ y := (mem_center_iff.1 hc y).symm
    have hcp : ⁅y, x⁆ ^ p = 1 := by
      rw [← commutatorElement_pow_left hcy, hyp, commutatorElement_one_left]
    have hdvd : p ∣ p.choose 2 :=
      hp.dvd_choose_self (by norm_num) (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
    obtain ⟨m, hm⟩ := hdvd
    rw [mul_pow_of_commute_commutator hcx hcy p, hxp, hyp, hm, pow_mul, hcp, one_pow]
    simp
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' := by
    rintro x ⟨hxZ, hxp⟩
    exact ⟨inv_mem hxZ, by rw [inv_pow, hxp, inv_one]⟩

end CFSG.RankThree.PartOne.Planes

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped commutatorElement

theorem pgOddSecondCenterPrimeTorsion : PGOddSecondCenterPrimeTorsion := by
  intro P _ _ p hp hp2 hP
  have hW : Subgroup.closure {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1} =
      Planes.torsionSecondCenter (P := P) p hp hp2 :=
    Subgroup.closure_eq (Planes.torsionSecondCenter (P := P) p hp hp2)
  have hmem : ∀ x : P, x ∈ Subgroup.closure
      {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1} ↔
      x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1 := fun x => by
    rw [hW]
    exact Iff.rfl
  refine ⟨?_, hmem, ?_, ?_⟩
  · rw [hW, Subgroup.characteristic_iff_comap_le]
    intro φ x hx
    obtain ⟨hxZ, hxp⟩ := hx
    have hxp' : φ x ^ p = 1 := hxp
    refine ⟨?_, φ.injective (by rw [map_pow, hxp', map_one])⟩
    have h := (Subgroup.characteristic_iff_comap_eq.1
      (inferInstance : (Subgroup.upperCentralSeries P 2).Characteristic)) φ
    rw [← h]
    exact hxZ
  · intro w hw g
    obtain ⟨hwZ, hwp⟩ := (hmem w).1 hw
    have hc : ⁅w, g⁆ ∈ center P := Planes.mem_upperCentralSeries_two_iff.1 hwZ g
    refine ⟨hc, ?_⟩
    rw [← Planes.commutatorElement_pow_left (mem_center_iff.1 hc w).symm, hwp,
      commutatorElement_one_left]
  · intro hnc hcyc
    have hpF : Fact p.Prime := ⟨hp⟩
    obtain ⟨U, V, hUV, hU, hUZ, hV, hVc, hVn, hcomm⟩ := Planes.exists_normal_plane hp hp2 hP hnc
    have hVW : V ≤ Subgroup.closure
        {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1} := by
      intro v hv
      rw [hmem]
      exact ⟨Planes.mem_upperCentralSeries_two_iff.2 fun y => hUZ (hcomm v hv y),
        ((Planes.isElementaryAbelian_iff p V).1 hV).2 v hv⟩
    exact Planes.not_isCyclic_of_isElementaryAbelian hp hVW hV (by rw [hVc]) hcyc

end CFSG.RankThree.PartOne
