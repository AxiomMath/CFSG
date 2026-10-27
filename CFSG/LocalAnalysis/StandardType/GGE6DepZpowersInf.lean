module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType.GGE6Dep

variable {G : Type} [Group G]

theorem zpowers_inf_eq_bot_of_centralizer {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (L : Set G)) (hxp : x ^ p = 1)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L)) : Subgroup.zpowers x ⊓ L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  rcases Subgroup.mem_inf.mp hz with ⟨hzpow, hzL⟩
  have hzC : z ∈ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hx hzpow
  let zL : ↥L := ⟨z, hzL⟩
  have hzcenter : zL ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    exact Subgroup.mem_centralizer_iff.mp hzC g.1 g.2
  rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨k, hk⟩
  have hzp : z ^ p = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hzLp : zL ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_one, hzp]
  have hdvd : orderOf zL ∣ p := orderOf_dvd_of_pow_eq_one hzLp
  rcases hp.eq_one_or_self_of_dvd (orderOf zL) hdvd with h1 | hp'
  · have hzL1 : zL = 1 := orderOf_eq_one_iff.mp h1
    exact Subtype.ext_iff.mp hzL1
  · exfalso
    have hcard : orderOf zL ∣ Nat.card ↥(Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hzcenter
    rw [hp'] at hcard
    exact hZ hcard

end CFSG.StandardType.GGE6Dep

end
