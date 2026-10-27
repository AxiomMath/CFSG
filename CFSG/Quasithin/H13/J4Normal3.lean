module

public import CFSG.Quasithin.H13.J4QuotGroup

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4

abbrev Zq
    : Subgroup QW := Subgroup.zpowers zq

abbrev CQ
    : Subgroup QW := Subgroup.centralizer (Zq : Set QW)

theorem zq_ne_one
    : zq ≠ 1 := localChecks_spec.1

theorem zq_pow_three
    : zq ^ 3 = 1 := localChecks_spec.2.1

theorem orderOf_zq
    : orderOf zq = 3 := orderOf_eq_prime zq_pow_three zq_ne_one

theorem card_Zq
    : Nat.card Zq = 3 := by rw [Nat.card_zpowers, orderOf_zq]

theorem conj_zq
    (g : QW) : g * zq * g⁻¹ = zq ∨ g * zq * g⁻¹ = zq⁻¹ := by
  let S : Subgroup QW :=
    { carrier := {g | g * zq * g⁻¹ = zq ∨ g * zq * g⁻¹ = zq⁻¹}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · left
          rw [mul_inv_rev, show a * b * zq * (b⁻¹ * a⁻¹) = a * (b * zq * b⁻¹) * a⁻¹ by group,
            hb, ha]
        · right
          rw [mul_inv_rev, show a * b * zq * (b⁻¹ * a⁻¹) = a * (b * zq * b⁻¹) * a⁻¹ by group,
            hb, show a * zq⁻¹ * a⁻¹ = (a * zq * a⁻¹)⁻¹ by group, ha]
        · right
          rw [mul_inv_rev, show a * b * zq * (b⁻¹ * a⁻¹) = a * (b * zq * b⁻¹) * a⁻¹ by group,
            hb, ha]
        · left
          rw [mul_inv_rev, show a * b * zq * (b⁻¹ * a⁻¹) = a * (b * zq * b⁻¹) * a⁻¹ by group,
            hb, show a * zq⁻¹ * a⁻¹ = (a * zq * a⁻¹)⁻¹ by group, ha, inv_inv]
      one_mem' := Or.inl (by group)
      inv_mem' := by
        rintro a (ha | ha)
        · left
          have h' : a * zq = zq * a := mul_inv_eq_iff_eq_mul.1 ha
          calc a⁻¹ * zq * a⁻¹⁻¹ = a⁻¹ * (zq * a) := by group
            _ = zq := by rw [← h']; group
        · right
          have h' : a * zq = zq⁻¹ * a := mul_inv_eq_iff_eq_mul.1 ha
          calc a⁻¹ * zq * a⁻¹⁻¹ = (a⁻¹ * (zq⁻¹ * a))⁻¹ := by group
            _ = zq⁻¹ := by rw [← h']; group }
  have hU : Uq ∈ S := Or.inr localChecks_spec.2.2.1
  have hV : Vq ∈ S := Or.inl (by rw [localChecks_spec.2.2.2.1]; group)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← closure_uvQ, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hU
    · exact hV
  have : g ∈ S := hS ▸ Subgroup.mem_top g
  exact this

theorem mem_CQ_iff
    {g : QW} : g ∈ CQ ↔ g * zq = zq * g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h zq (Subgroup.mem_zpowers zq)).symm
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute zq g from h.symm) k)).eq

theorem Uq_not_mem_CQ
    : Uq ∉ CQ := by
  intro h
  have e := mem_CQ_iff.1 h
  have : Uq * zq * Uq⁻¹ = zq := by rw [e]; group
  rw [localChecks_spec.2.2.1] at this
  apply zq_ne_one
  have h2 : zq * zq = 1 := by
    calc zq * zq = zq * zq⁻¹⁻¹ := by rw [inv_inv]
      _ = 1 := by rw [this, mul_inv_cancel]
  rw [← zq_pow_three, pow_succ, sq, h2, one_mul]

theorem not_mem_CQ_iff
    {g : QW} : g ∉ CQ ↔ g * zq * g⁻¹ = zq⁻¹ := by
  rw [mem_CQ_iff]
  constructor
  · intro h
    rcases conj_zq g with h1 | h1
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h1) h
    · exact h1
  · intro h e
    have : g * zq * g⁻¹ = zq := by rw [e]; group
    rw [this] at h
    apply zq_ne_one
    have h2 : zq * zq = 1 := by
      calc zq * zq = zq * zq⁻¹⁻¹ := by rw [inv_inv]
        _ = 1 := by rw [← h, mul_inv_cancel]
    rw [← zq_pow_three, pow_succ, sq, h2, one_mul]

instance Zq_normal
    : Zq.Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← conj_zpow]
  rcases conj_zq g with h | h <;> rw [h]
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zq) k
  · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers zq)) k

theorem index_CQ
    : CQ.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨Uq, fun b => ?_⟩
  by_cases hb : b ∈ CQ
  · refine Or.inr ⟨hb, fun hbU => ?_⟩
    have h1 := mem_CQ_iff.1 hbU
    have h2 := mem_CQ_iff.1 hb
    apply Uq_not_mem_CQ
    rw [mem_CQ_iff]
    have : Uq = b⁻¹ * (b * Uq) := by group
    rw [this, mul_assoc, h1, ← mul_assoc, show b⁻¹ * zq = zq * b⁻¹ by
      calc b⁻¹ * zq = b⁻¹ * (zq * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * zq) * b⁻¹ := by rw [h2]
        _ = zq * b⁻¹ := by group, mul_assoc]
  · refine Or.inl ⟨?_, hb⟩
    rw [mem_CQ_iff]
    have h1 := not_mem_CQ_iff.1 hb
    have h2 := localChecks_spec.2.2.1
    have : b * Uq * zq * (b * Uq)⁻¹ = zq := by
      calc b * Uq * zq * (b * Uq)⁻¹ = b * (Uq * zq * Uq⁻¹) * b⁻¹ := by group
        _ = (b * zq * b⁻¹)⁻¹ := by rw [h2]; group
        _ = zq := by rw [h1, inv_inv]
    calc b * Uq * zq = b * Uq * zq * (b * Uq)⁻¹ * (b * Uq) := by group
      _ = zq * (b * Uq) := by rw [this]

instance CQ_normal
    : CQ.Normal := Subgroup.normal_of_index_eq_two index_CQ

theorem Zq_le_CQ
    : Zq ≤ CQ := by
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [mem_CQ_iff]
  exact (Commute.zpow_left (Commute.refl zq) k).eq

end CFSG.Quasithin.H13.J4
