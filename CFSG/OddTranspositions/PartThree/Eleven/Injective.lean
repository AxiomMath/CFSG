module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem s11i_commute_of_orderOf_mul_dvd_two {M : Type*} [Group M] {x y : M}
    (hx : x * x = 1) (hy : y * y = 1) (h : orderOf (x * y) ∣ 2) : x * y = y * x := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_two] at h
  have h1 := eq_inv_of_mul_eq_one_left h
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy] at h1

theorem injOn_mk_DstarH (hC : HypothesisC D)
    (hZ : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha))
    (hnc : ∀ a ∈ imageClass hC, ∃ b ∈ imageClass hC, ¬ Commute a b) :
    Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (DstarH hC) := by
  intro x hx y hy hq
  set z : Halpha D hC.alpha := x⁻¹ * y with hzdef
  have hzK : z ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [hzdef]
    exact QuotientGroup.eq.mp hq
  have hzcenter : z ∈ Subgroup.center (Halpha D hC.alpha) := hZ ▸ hzK
  have hzcomm : ∀ g : Halpha D hC.alpha, Commute z g := fun g =>
    ((Subgroup.mem_center_iff.mp hzcenter) g).symm
  by_contra hne
  have hz1 : z ≠ 1 := by
    intro h
    apply hne
    have hyx : y = x := by
      calc y = x * z := by rw [hzdef]; group
        _ = x * 1 := by rw [h]
        _ = x := by rw [mul_one]
    exact hyx.symm
  have hxord : orderOf x = 2 := (DstarH_isOddTransp hC).1 x hx
  have hyord : orderOf y = 2 := (DstarH_isOddTransp hC).1 y hy
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hxord] at h
    simpa [pow_two] using h
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hyord] at h
    simpa [pow_two] using h
  have hy_eq : y = x * z := by rw [hzdef]; group
  have hz2 : z * z = 1 := by
    have h1 : y ^ 2 = x ^ 2 * z ^ 2 := by
      rw [hy_eq, (hzcomm x).symm.mul_pow 2]
    have hx2p : x ^ 2 = 1 := by simpa [pow_two] using hx2
    have hy2p : y ^ 2 = 1 := by simpa [pow_two] using hy2
    rw [hx2p, one_mul, hy2p] at h1
    simpa [pow_two] using h1.symm
  have hzord : orderOf z = 2 := by
    apply orderOf_eq_prime
    · simpa [pow_two] using hz2
    · exact hz1
  obtain ⟨b, hb, hnb⟩ := hnc (QuotientGroup.mk' _ x) ⟨x, hx, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hb
  have hncxw : ¬ Commute x w := fun hcomm => hnb (hcomm.map (QuotientGroup.mk' _))
  have hword : orderOf w = 2 := (DstarH_isOddTransp hC).1 w hw
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hword] at h
    simpa [pow_two] using h
  have hnotdvd : ¬ orderOf (x * w) ∣ 2 := by
    intro hd
    exact hncxw (s11i_commute_of_orderOf_mul_dvd_two hx2 hw2 hd)
  have hodd : Odd (orderOf (x * w)) := by
    rcases (DstarH_isOddTransp hC).2 x hx w hw with h | h
    · exact absurd h hnotdvd
    · exact h
  have hm1 : orderOf (x * w) ≠ 1 := by
    intro h
    apply hncxw
    have hxw : x * w = 1 := orderOf_eq_one_iff.mp h
    have hxw' : x = w := by
      rw [eq_inv_of_mul_eq_one_left hxw, inv_eq_self_of_orderOf_eq_two hword]
    rw [hxw']
  have hyw : y * w = (x * w) * z := by
    rw [hy_eq]
    calc (x * z) * w = x * (z * w) := by rw [mul_assoc]
      _ = x * (w * z) := by rw [(hzcomm w).eq]
      _ = (x * w) * z := by rw [← mul_assoc]
  have hcomm_xw_z : Commute (x * w) z := (hzcomm (x * w)).symm
  have hcop : (orderOf (x * w)).Coprime (orderOf z) := by
    rw [hzord]
    exact hodd.coprime_two_right
  have hord_yw : orderOf (y * w) = 2 * orderOf (x * w) := by
    rw [hyw, hcomm_xw_z.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hzord, Nat.mul_comm]
  rcases (DstarH_isOddTransp hC).2 y hy w hw with hdvd | hodd_yw
  · rw [hord_yw] at hdvd
    have hm_dvd_one : orderOf (x * w) ∣ 1 :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp (by simpa using hdvd)
    exact hm1 (Nat.dvd_one.mp hm_dvd_one)
  · rw [hord_yw] at hodd_yw
    exact hodd_yw.not_two_dvd_nat (dvd_mul_right 2 _)

end CFSG.OddTranspositions.PartThree
