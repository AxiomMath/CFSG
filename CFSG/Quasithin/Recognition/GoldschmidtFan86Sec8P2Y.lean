module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem y_zero (δ' : V) : D.y δ' 0 = L.z (D.delta 0) * L.z δ' := by
  simp [D10Set.y]

theorem y_shift (δ' : V) (i : Fin 5) : D.x⁻¹ * D.y δ' i * D.x = D.y δ' (i + 1) := by
  have h5 := D.x_pow_five
  by_cases hi : i = 4
  · subst hi
    have e : ((4 : Fin 5) + 1) = 0 := by decide
    rw [e, y_zero]
    show D.x⁻¹ * ((D.x ^ (4 : Fin 5).val)⁻¹ * (L.z (D.delta 0) * L.z δ') *
      D.x ^ (4 : Fin 5).val) * D.x = _
    have : (4 : Fin 5).val = 4 := rfl
    rw [this]
    calc D.x⁻¹ * ((D.x ^ 4)⁻¹ * (L.z (D.delta 0) * L.z δ') * D.x ^ 4) * D.x
        = (D.x ^ 4 * D.x)⁻¹ * (L.z (D.delta 0) * L.z δ') * (D.x ^ 4 * D.x) := by group
      _ = _ := by rw [← pow_succ, h5]; simp
  · have hlt : i.val < 4 := by
      have : i.val ≠ 4 := fun h => hi (Fin.ext h)
      have := i.2
      omega
    have e : ((i + 1 : Fin 5) : ℕ) = i.val + 1 := by
      rw [Fin.val_add_one_of_lt]
      exact Fin.lt_def.2 hlt
    show D.x⁻¹ * ((D.x ^ i.val)⁻¹ * (L.z (D.delta 0) * L.z δ') * D.x ^ i.val) * D.x =
      (D.x ^ ((i + 1 : Fin 5) : ℕ))⁻¹ * (L.z (D.delta 0) * L.z δ') *
        D.x ^ ((i + 1 : Fin 5) : ℕ)
    rw [e, pow_succ]
    group

open Fin.NatCast Fin.CommRing in
theorem y_conj_pow (δ' : V) (n : ℕ) (i : Fin 5) :
    (D.x ^ n)⁻¹ * D.y δ' i * D.x ^ n = D.y δ' (i + (n : Fin 5)) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have h1 := ih i
    have h2 := D.y_shift δ' (i + (n : Fin 5))
    rw [pow_succ, mul_inv_rev]
    calc D.x⁻¹ * (D.x ^ n)⁻¹ * D.y δ' i * (D.x ^ n * D.x)
        = D.x⁻¹ * ((D.x ^ n)⁻¹ * D.y δ' i * D.x ^ n) * D.x := by group
      _ = D.y δ' (i + ((n + 1 : ℕ) : Fin 5)) := by
        rw [h1]
        have : i + ((n + 1 : ℕ) : Fin 5) = i + (n : Fin 5) + 1 := by
          push_cast
          ring
        rw [this]
        exact h2

theorem z0_comm_zp (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') :
    L.z (D.delta 0) * L.z δ' = L.z δ' * L.z (D.delta 0) := by
  refine h.z_comm_of_dist_le (D.valence_delta F 0) (D.valence_ypair F hY) ?_
  have h1 := F.isTree.connected.dist_triangle (u := D.delta 0) (v := D.alpha 0) (w := δ')
  have h2 : Γ.dist (D.delta 0) (D.alpha 0) = 2 := by
    rw [SimpleGraph.dist_comm, D.dist_alpha_delta F 0]
  have h3 : Γ.dist (D.alpha 0) δ' = 2 := hY.2.2.2.2.1
  omega

open Fin.NatCast Fin.CommRing in
theorem y_refl_nat (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') (n : ℕ) :
    L.z (D.delta 0) * D.y δ' (n : Fin 5) * L.z (D.delta 0) = D.y δ' (-(n : Fin 5)) := by
  have ha2 := D.zd_mul_self F 0
  have hax := D.zd_x_inv F
  have ha_inv : (L.z (D.delta 0))⁻¹ = L.z (D.delta 0) := L.z_inv (D.valence_delta F 0)
  have hxa : L.z (D.delta 0) * D.x⁻¹ * L.z (D.delta 0) = D.x := by
    calc L.z (D.delta 0) * D.x⁻¹ * L.z (D.delta 0)
        = L.z (D.delta 0) * (L.z (D.delta 0) * D.x * L.z (D.delta 0)) * L.z (D.delta 0) := by
          rw [hax]
      _ = (L.z (D.delta 0) * L.z (D.delta 0)) * D.x * (L.z (D.delta 0) * L.z (D.delta 0)) := by
          group
      _ = D.x := by rw [ha2, one_mul, mul_one]
  have hc := D.z0_comm_zp F h hY
  induction n with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, y_zero]
    calc L.z (D.delta 0) * (L.z (D.delta 0) * L.z δ') * L.z (D.delta 0)
        = (L.z (D.delta 0) * L.z (D.delta 0)) * (L.z δ' * L.z (D.delta 0)) := by group
      _ = L.z (D.delta 0) * L.z δ' := by rw [ha2, one_mul, ← hc]
  | succ n ih =>
    have hc1 : D.x⁻¹ * D.y δ' (n : Fin 5) * D.x = D.y δ' ((n : Fin 5) + 1) :=
      D.y_shift δ' (n : Fin 5)
    have hc2 : D.x⁻¹ * D.y δ' (-(n : Fin 5) - 1) * D.x = D.y δ' (-(n : Fin 5) - 1 + 1) :=
      D.y_shift δ' _
    have hneg : -(n : Fin 5) - 1 + 1 = -(n : Fin 5) := by ring
    rw [hneg] at hc2
    have hidx : ((n + 1 : ℕ) : Fin 5) = (n : Fin 5) + 1 := by push_cast; ring
    have hidx2 : -((n : Fin 5) + 1) = -(n : Fin 5) - 1 := by ring
    have e1 : D.y δ' (-(n : Fin 5) - 1) = D.x * D.y δ' (-(n : Fin 5)) * D.x⁻¹ := by
      calc D.y δ' (-(n : Fin 5) - 1)
          = D.x * (D.x⁻¹ * D.y δ' (-(n : Fin 5) - 1) * D.x) * D.x⁻¹ := by group
        _ = D.x * D.y δ' (-(n : Fin 5)) * D.x⁻¹ := by rw [hc2]
    rw [hidx, hidx2, ← hc1, e1, ← ih]
    have key : L.z (D.delta 0) * (D.x⁻¹ * D.y δ' (n : Fin 5) * D.x) * (L.z (D.delta 0))⁻¹ =
        (L.z (D.delta 0) * D.x⁻¹ * (L.z (D.delta 0))⁻¹) *
        (L.z (D.delta 0) * D.y δ' (n : Fin 5) * (L.z (D.delta 0))⁻¹) *
        (L.z (D.delta 0) * D.x * (L.z (D.delta 0))⁻¹) := by group
    rw [ha_inv, hxa, hax] at key
    rw [key]

open Fin.NatCast Fin.CommRing in
theorem y_refl (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') (k i : Fin 5) :
    L.z (D.delta k) * D.y δ' i * L.z (D.delta k) = D.y δ' (2 * k - i) := by
  have hk : ((k.val : ℕ) : Fin 5) = k := Fin.cast_val_eq_self k
  have h1 : (D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val = L.z (D.delta k) := by
    have := D.zd_conj_pow k.val 0
    rwa [hk, zero_add] at this
  have h2 : (D.x ^ k.val)⁻¹ * D.y δ' (i - k) * D.x ^ k.val = D.y δ' i := by
    have := D.y_conj_pow δ' k.val (i - k)
    rwa [hk, sub_add_cancel] at this
  have h3 : L.z (D.delta 0) * D.y δ' (i - k) * L.z (D.delta 0) = D.y δ' (-(i - k)) := by
    have := D.y_refl_nat F h hY (i - k).val
    rwa [Fin.cast_val_eq_self] at this
  have h4 : (D.x ^ k.val)⁻¹ * D.y δ' (-(i - k)) * D.x ^ k.val = D.y δ' (-(i - k) + k) := by
    have := D.y_conj_pow δ' k.val (-(i - k))
    rwa [hk] at this
  calc L.z (D.delta k) * D.y δ' i * L.z (D.delta k)
      = ((D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val) *
        ((D.x ^ k.val)⁻¹ * D.y δ' (i - k) * D.x ^ k.val) *
        ((D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val) := by rw [h1, h2]
    _ = (D.x ^ k.val)⁻¹ * (L.z (D.delta 0) * D.y δ' (i - k) * L.z (D.delta 0)) *
        D.x ^ k.val := by group
    _ = D.y δ' (2 * k - i) := by
      rw [h3, h4]
      congr 2
      ring

end D10Set

end CFSG.Quasithin.Fan86
