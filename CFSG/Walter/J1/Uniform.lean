module

public import CFSG.Walter.J1.HSeven

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

omit [Finite G] in
theorem ncard_inv_conj (y g : G) :
    {u : G | orderOf u = 2 ∧ u * (g * y * g⁻¹) * u⁻¹ = (g * y * g⁻¹)⁻¹}.ncard =
      {u : G | orderOf u = 2 ∧ u * y * u⁻¹ = y⁻¹}.ncard := by
  refine Set.ncard_congr (fun u _ => g⁻¹ * u * g) ?_ ?_ ?_
  · rintro u ⟨hu, huy⟩
    refine ⟨by rw [show g⁻¹ * u * g = g⁻¹ * u * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hu], ?_⟩
    calc g⁻¹ * u * g * y * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * (g * y * g⁻¹) * u⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹)⁻¹ * g := by rw [huy]
      _ = y⁻¹ := by group
  · intro u v _ _ huv
    have := congrArg (fun z => g * z * g⁻¹) huv
    simpa [mul_assoc] using this
  · rintro v ⟨hv, hvy⟩
    refine ⟨g * v * g⁻¹, ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hv], ?_⟩, by group⟩
    calc g * v * g⁻¹ * (g * y * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * (v * y * v⁻¹) * g⁻¹ := by group
      _ = g * y⁻¹ * g⁻¹ := by rw [hvy]
      _ = (g * y * g⁻¹)⁻¹ := by group

omit [Finite G] in
theorem inv_iff_of_mem_zpowers {p : ℕ} (hp : p.Prime) {y z : G} (hy : orderOf y = p)
    (hz : z ∈ Subgroup.zpowers y) (hz1 : z ≠ 1) (u : G) :
    u * z * u⁻¹ = z⁻¹ ↔ u * y * u⁻¹ = y⁻¹ := by
  have hZ : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have hyz : y ∈ Subgroup.zpowers z := by
    rw [← eq_zpowers_of_card_prime hp hZ hz hz1]
    exact Subgroup.mem_zpowers y
  constructor
  · intro h1
    obtain ⟨k, rfl⟩ := hyz
    change u * z ^ k * u⁻¹ = (z ^ k)⁻¹
    rw [← conj_zpow, h1, inv_zpow]
  · intro h1
    obtain ⟨k, rfl⟩ := hz
    change u * y ^ k * u⁻¹ = (y ^ k)⁻¹
    rw [← conj_zpow, h1, inv_zpow]

include h in
theorem ncard_inv_seven_eq (Q : Sylow 2 G) {y y' : G}
    (hy : y ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (hy' : y' ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (h7 : orderOf y = 7)
    (h7' : orderOf y' = 7) :
    {u : G | orderOf u = 2 ∧ u * y * u⁻¹ = y⁻¹}.ncard =
      {u : G | orderOf u = 2 ∧ u * y' * u⁻¹ = y'⁻¹}.ncard := by
  obtain ⟨g, -, hg⟩ := h.exists_conj_seven Q hy hy' h7 h7'
  have hg1 : g * y * g⁻¹ ≠ 1 := by
    intro h1
    have : y = 1 := by
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at h7
    omega
  rw [← ncard_inv_conj y g]
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  rw [inv_iff_of_mem_zpowers (by norm_num) h7' hg hg1]

include h in
theorem not_mem_of_inv (Q : Sylow 2 G) {u x : G}
    (hu : orderOf u = 2) (huH : u ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (hxH : x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (hx : orderOf x = 3 ∨ orderOf x = 6 ∨ orderOf x = 7) (hux : u * x * u⁻¹ = x⁻¹) : False := by
  have huQ := mem_sylow_of_orderOf_eq_two Q huH hu
  have hc : x⁻¹ * x⁻¹ ∈ (Q : Subgroup G) := by
    have h1 : x * u⁻¹ * x⁻¹ ∈ (Q : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hxH _).mp (Subgroup.inv_mem _ huQ)
    have h2 : u * (x * u⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ := by
      calc u * (x * u⁻¹ * x⁻¹) = (u * x * u⁻¹) * x⁻¹ := by group
        _ = x⁻¹ * x⁻¹ := by rw [hux]
    rw [← h2]
    exact Subgroup.mul_mem _ huQ h1
  have h4 : x ^ 4 = 1 := by
    have := h.mul_self_of_mem_sylow' Q hc
    have h5 : (x ^ 4)⁻¹ = 1 := by
      rw [← this]
      group
    exact inv_eq_one.mp h5
  have := orderOf_dvd_of_pow_eq_one h4
  rcases hx with h0 | h0 | h0 <;> rw [h0] at this <;> norm_num at this

end JankoHyp

end CFSG.Walter.J1
