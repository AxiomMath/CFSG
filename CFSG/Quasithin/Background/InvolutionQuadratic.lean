module

public import CFSG.Quasithin.Background.CommVZ4

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem commV_zpowers_le_fixV_of_involution (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} (hx : x ^ 2 = 1) :
    commV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers x) := by
  have hinv : ∀ u : V, u⁻¹ = u := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV u)
  have hxx : ∀ v : V, x (x v) = v := fun v => by
    have := congrArg (fun g : MulAut V => g v) hx
    simpa [pow_two, MulAut.mul_apply] using this
  have hz : ∀ y ∈ Subgroup.zpowers x, y = 1 ∨ y = x := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact CommVZ4.zpow_eq_one_or_self_of_sq hx n
  have key : ∀ w ∈ commV (Subgroup.zpowers x), x w = w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨z, hz', v, rfl⟩ := hw
      rcases hz z hz' with h | h
      · rw [h]; simp
      · rw [h, map_mul, map_inv, hxx, hinv (x v), hinv v]
        exact mul_comm _ _
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, ha]
  intro w hw y hy
  rcases hz y hy with h | h
  · rw [h]; simp
  · rw [h]; exact key w hw

end CFSG.Quasithin
