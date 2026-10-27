module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Refl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem d5_center : ∀ g : DihedralGroup 5, (∀ d : DihedralGroup 5, g * d = d * g) → g = 1 := by
  decide

theorem d5_prod : ∀ u v : DihedralGroup 5, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v →
    (u * v) ^ 5 = 1 ∧ u * v ≠ 1 := by
  decide

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem x_pow_five : D.x ^ 5 = 1 := by
  open Fin.NatCast in
  obtain ⟨e⟩ := D.dih
  have hz : ∀ i, L.z (D.delta i) ∈
      Subgroup.closure (Set.range fun i => L.z ((D.P i).vert 4)) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  have hx : D.x ^ 5 ∈ Subgroup.closure (Set.range fun i => L.z ((D.P i).vert 4)) :=
    pow_mem (Subgroup.mul_mem _ (hz 2) (hz 0)) 5
  have hgen : ∀ i, D.x ^ 5 * L.z (D.delta i) = L.z (D.delta i) * D.x ^ 5 := by
    intro i
    have h1 := D.zd_conj_pow 5 i
    have h5 : ((5 : ℕ) : Fin 5) = 0 := by decide
    rw [h5, add_zero] at h1
    calc D.x ^ 5 * L.z (D.delta i)
        = D.x ^ 5 * ((D.x ^ 5)⁻¹ * L.z (D.delta i) * D.x ^ 5) := by rw [h1]
      _ = L.z (D.delta i) * D.x ^ 5 := by group
  have hcen : ∀ k ∈ Subgroup.closure (Set.range fun i => L.z ((D.P i).vert 4)),
      D.x ^ 5 * k = k * D.x ^ 5 := by
    intro k hk
    refine Subgroup.closure_induction (p := fun k _ => D.x ^ 5 * k = k * D.x ^ 5) ?_ ?_ ?_ ?_ hk
    · rintro _ ⟨i, rfl⟩
      exact hgen i
    · simp
    · intro a b _ _ ha hb
      rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
    · intro a _ ha
      calc D.x ^ 5 * a⁻¹ = a⁻¹ * (a * D.x ^ 5) * a⁻¹ := by group
        _ = a⁻¹ * (D.x ^ 5 * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * D.x ^ 5 := by group
  have hy : e ⟨D.x ^ 5, hx⟩ = 1 := by
    apply d5_center
    intro d
    obtain ⟨k, rfl⟩ := e.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcen k k.2)
  have := e.injective (hy.trans (map_one e).symm)
  exact congrArg Subtype.val this

theorem x_ne_one (F : FanTree Γ G) : D.x ≠ 1 := by
  intro h1
  have h2 : L.z (D.delta 2) * L.z (D.delta 0) = 1 := h1
  have h3 : L.z (D.delta 2) = L.z (D.delta 0) := by
    calc L.z (D.delta 2) = L.z (D.delta 2) * L.z (D.delta 0) * L.z (D.delta 0) := by
          rw [mul_assoc, D.zd_mul_self F 0, mul_one]
      _ = L.z (D.delta 0) := by rw [h2, one_mul]
  exact absurd (D.inj h3) (by decide)

theorem orderOf_x (F : FanTree Γ G) : orderOf D.x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime D.x_pow_five (D.x_ne_one F)

open Fin.NatCast in
theorem x_pow_inv_smul_vert (F : FanTree Γ G) (h : Fan71c F L) (n : ℕ) (i : Fin 5) {m : ℕ}
    (hm : m ≤ 4) : (D.x ^ n)⁻¹ • (D.P i).vert m = (D.P (i + (n : Fin 5))).vert m := by
  open Fin.CommRing in
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_inv_rev, mul_smul, ih i, D.x_inv_smul_vert F h _ hm]
    have : i + (n : Fin 5) + 1 = i + ((n + 1 : ℕ) : Fin 5) := by
      push_cast
      ring
    rw [this]

end D10Set

end CFSG.Quasithin.Fan86
