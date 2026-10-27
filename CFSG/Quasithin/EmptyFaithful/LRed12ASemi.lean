module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

namespace LRed12

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem lred12_inv_eq_self (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v := by
  have := hV v
  rw [pow_two, mul_eq_one_iff_eq_inv] at this
  exact this.symm

private theorem lred12_eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {u : G} (hu2 : u ^ 2 = 1)
    {x : G} (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : u ^ (2 : ℤ) = 1 := by simpa using hu2
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

omit [Finite V] in
private theorem lred12_apply_apply {u : MulAut V} (hu2 : u ^ 2 = 1) (v : V) : u (u v) = v := by
  rw [← MulAut.mul_apply, ← pow_two, hu2]
  rfl

omit [Finite V] in
private theorem lred12_mul_apply_mul_apply_apply {U : Subgroup V} {z : MulAut V} (hz3 : z ^ 3 = 1)
    (hUz : ∀ w ∈ U, z w ∈ U) (hfpf : ∀ w ∈ U, z w = w → w = 1) {w : V} (hw : w ∈ U) :
    w * z w * z (z w) = 1 := by
  have h3 : z (z (z w)) = w := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hz3]
    rfl
  refine hfpf _ (U.mul_mem (U.mul_mem hw (hUz w hw)) (hUz _ (hUz w hw))) ?_
  rw [map_mul, map_mul, h3]
  ac_rfl

omit [Finite V] in
private theorem lred12_mem_commSub_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
    {z u : MulAut V} (hz3 : z ^ 3 = 1) (huz : u * z * u⁻¹ = z⁻¹)
    (hUz : ∀ w ∈ U, z w ∈ U) (hfpf : ∀ w ∈ U, z w = w → w = 1) {v : V} (hv : v ∈ U)
    (huv : u v = v) : v ∈ commSub U (Subgroup.zpowers u) := by
  have hzz : z * z = z⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← pow_three, hz3])
  have huz' : u * z = z⁻¹ * u := by
    rw [← huz]
    group
  have h1 : u (z v) = z (z v) := by
    calc u (z v) = (u * z) v := rfl
      _ = (z⁻¹ * u) v := by rw [huz']
      _ = z⁻¹ (u v) := rfl
      _ = (z * z) v := by rw [huv, hzz]
      _ = z (z v) := rfl
  have h2 := lred12_mul_apply_mul_apply_apply hz3 hUz hfpf hv
  have h3 : z v * z (z v) = v := by
    rw [← lred12_inv_eq_self hV v]
    exact eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, lred12_inv_eq_self hV v]; exact h2)
  have h4 : u (z v) * (z v)⁻¹ = v := by
    rw [h1, lred12_inv_eq_self hV (z v), mul_comm, h3]
  rw [← h4]
  exact Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers u, z v, hUz v hv, rfl⟩

omit [Finite V] in
theorem commSub_zpowers_eq_inf_fixV_of_inverts (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
    {z u : MulAut V} (hz3 : z ^ 3 = 1) (hu2 : u ^ 2 = 1) (huz : u * z * u⁻¹ = z⁻¹)
    (hUu : ∀ w ∈ U, u w ∈ U) (hUz : ∀ w ∈ U, z w ∈ U)
    (hfpf : ∀ w ∈ U, z w = w → w = 1) :
    commSub U (Subgroup.zpowers u) = U ⊓ fixV (Subgroup.zpowers u) := by
  refine le_antisymm ?_ fun v hv => ?_
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    rcases lred12_eq_one_or_eq_of_mem_zpowers hu2 hx with h | h
    · rw [h]
      simp
    · rw [h]
      refine ⟨U.mul_mem (hUu w hw) (U.inv_mem hw), mem_fixV_zpowers_iff.mpr ?_⟩
      rw [map_mul, map_inv, lred12_apply_apply hu2, lred12_inv_eq_self hV,
        lred12_inv_eq_self hV, mul_comm]
  · exact lred12_mem_commSub_of_fixed hV hz3 huz hUz hfpf hv.1 (mem_fixV_zpowers_iff.mp hv.2)

theorem rk_eq_two_mul_rk_commSub_of_inverts (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
    {z u : MulAut V} (hz3 : z ^ 3 = 1) (hu2 : u ^ 2 = 1) (huz : u * z * u⁻¹ = z⁻¹)
    (hUu : ∀ w ∈ U, u w ∈ U) (hUz : ∀ w ∈ U, z w ∈ U)
    (hfpf : ∀ w ∈ U, z w = w → w = 1) :
    rk U = 2 * rk (commSub U (Subgroup.zpowers u)) := by
  have hinv : ∀ x ∈ Subgroup.zpowers u, ∀ w ∈ U, x w ∈ U := by
    intro x hx w hw
    rcases lred12_eq_one_or_eq_of_mem_zpowers hu2 hx with h | h
    · rw [h]
      exact hw
    · rw [h]
      exact hUu w hw
  have h := rk_commSub_add_rk_inf_fixV hinv
  rw [← commSub_zpowers_eq_inf_fixV_of_inverts hV hz3 hu2 huz hUu hUz hfpf] at h
  omega

theorem rk_le_two_mul_rk_commSub_of_inverts (hV : ∀ v : V, v ^ 2 = 1) {W U : Subgroup V}
    {z u : MulAut V} (hz3 : z ^ 3 = 1) (hu2 : u ^ 2 = 1) (huz : u * z * u⁻¹ = z⁻¹)
    (hUW : U ≤ W) (hUu : ∀ w ∈ U, u w ∈ U) (hUz : ∀ w ∈ U, z w ∈ U)
    (hfpf : ∀ w ∈ U, z w = w → w = 1) :
    rk U ≤ 2 * rk (commSub W (Subgroup.zpowers u)) := by
  rw [rk_eq_two_mul_rk_commSub_of_inverts hV hz3 hu2 huz hUu hUz hfpf]
  exact Nat.mul_le_mul_left 2 (rk_mono (commSub_mono hUW le_rfl))

end LRed12

end CFSG.Quasithin
