module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.GGE6Dep

variable {G : Type} [Group G]

theorem mem_of_conj_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) {L N : Subgroup G} {u n : G}
    (hNL : N ≤ L) (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L)) (hnN : n ∈ N) (huL : u ∈ L)
    (hup : u ^ p = 1) (hc : ∀ l ∈ L, n * l * n⁻¹ = u * l * u⁻¹) : u ∈ N := by
  set z : G := u⁻¹ * n with hzdef
  have hzL : z ∈ L := L.mul_mem (L.inv_mem huL) (hNL hnN)
  have hz_comm : ∀ l ∈ L, l * z = z * l := by
    intro l hl
    have hzl : z * l * z⁻¹ = l := by
      have h' : u⁻¹ * (n * l * n⁻¹) * u = l := by
        rw [hc l hl]
        group
      rw [hzdef, mul_inv_rev, inv_inv]
      rwa [show u⁻¹ * n * l * (n⁻¹ * u) = u⁻¹ * (n * l * n⁻¹) * u by group]
    have hzl' : z * l = l * z := by
      calc z * l = z * l * z⁻¹ * z := by group
        _ = l * z := by rw [hzl]
    exact hzl'.symm
  let zL : ↥L := ⟨z, hzL⟩
  have hzCent : zL ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hz_comm (g : G) g.2
  have hdvdZ : orderOf zL ∣ Nat.card ↥(Subgroup.center ↥L) :=
    Subgroup.orderOf_dvd_natCard _ hzCent
  have horder : orderOf zL = orderOf z := Subgroup.orderOf_mk z hzL
  have hnotdvd : ¬ p ∣ orderOf z := by
    intro hpdvd
    apply hZ
    rw [← horder] at hpdvd
    exact hpdvd.trans hdvdZ
  have hcop : Nat.Coprime p (orderOf z) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdvd
  have hzu : Commute u z := by
    have h := (Subgroup.mem_center_iff.mp hzCent) ⟨u, huL⟩
    exact congrArg Subtype.val h
  have hnuz : u * z = n := by
    rw [hzdef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hnp : n ^ p = z ^ p := by
    rw [← hnuz, hzu.mul_pow p, hup, one_mul]
  have hzmem : z ∈ Subgroup.zpowers (z ^ p) := by
    rw [mem_zpowers_pow_iff]
    exact hcop
  have hzN : z ∈ N := by
    have hmem : z ∈ Subgroup.zpowers (n ^ p) := by
      rw [hnp]
      exact hzmem
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem N hnN p) hmem
  rw [show u = n * z⁻¹ by rw [← hnuz, mul_assoc, mul_inv_cancel, mul_one]]
  exact N.mul_mem hnN (N.inv_mem hzN)

end CFSG.StandardType.GGE6Dep

end
