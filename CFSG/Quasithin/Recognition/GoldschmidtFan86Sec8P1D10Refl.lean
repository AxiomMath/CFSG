module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem zd_mul_self (F : FanTree Γ G) (i : Fin 5) :
    L.z (D.delta i) * L.z (D.delta i) = 1 :=
  L.z_mul_self (D.valence_delta F i)

theorem zd_x_inv (F : FanTree Γ G) :
    L.z (D.delta 0) * D.x * L.z (D.delta 0) = D.x⁻¹ := by
  have h0 := D.zd_mul_self F 0
  have hx : D.x = L.z (D.delta 2) * L.z (D.delta 0) := rfl
  have e : D.x⁻¹ = L.z (D.delta 0) * L.z (D.delta 2) := by
    rw [hx, mul_inv_rev, L.z_inv (D.valence_delta F 0), L.z_inv (D.valence_delta F 2)]
  rw [e, hx]
  calc L.z (D.delta 0) * (L.z (D.delta 2) * L.z (D.delta 0)) * L.z (D.delta 0)
      = L.z (D.delta 0) * L.z (D.delta 2) * (L.z (D.delta 0) * L.z (D.delta 0)) := by group
    _ = L.z (D.delta 0) * L.z (D.delta 2) := by rw [h0, mul_one]

open Fin.NatCast Fin.CommRing in
theorem zd_conj_pow (n : ℕ) (i : Fin 5) :
    (D.x ^ n)⁻¹ * L.z (D.delta i) * D.x ^ n = L.z (D.delta (i + (n : Fin 5))) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have h1 := ih i
    have h2 := D.conj (i + (n : Fin 5))
    rw [pow_succ, mul_inv_rev]
    calc D.x⁻¹ * (D.x ^ n)⁻¹ * L.z (D.delta i) * (D.x ^ n * D.x)
        = D.x⁻¹ * ((D.x ^ n)⁻¹ * L.z (D.delta i) * D.x ^ n) * D.x := by group
      _ = L.z (D.delta (i + ((n + 1 : ℕ) : Fin 5))) := by
        rw [h1]
        have : i + ((n + 1 : ℕ) : Fin 5) = i + (n : Fin 5) + 1 := by
          push_cast
          ring
        rw [this]
        exact h2

open Fin.NatCast Fin.CommRing in
theorem zd_refl_nat (F : FanTree Γ G) (n : ℕ) :
    L.z (D.delta 0) * L.z (D.delta (n : Fin 5)) * L.z (D.delta 0) =
      L.z (D.delta (-(n : Fin 5))) := by
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
  induction n with
  | zero => simp [ha2]
  | succ n ih =>
    have hc : D.x⁻¹ * L.z (D.delta (n : Fin 5)) * D.x = L.z (D.delta ((n : Fin 5) + 1)) :=
      D.conj (n : Fin 5)
    have hc' : D.x⁻¹ * L.z (D.delta (-(n : Fin 5) - 1)) * D.x =
        L.z (D.delta (-(n : Fin 5) - 1 + 1)) := D.conj _
    have hidx : ((n + 1 : ℕ) : Fin 5) = (n : Fin 5) + 1 := by push_cast; ring
    have hidx2 : -((n : Fin 5) + 1) = -(n : Fin 5) - 1 := by ring
    have hneg : -(n : Fin 5) - 1 + 1 = -(n : Fin 5) := by ring
    rw [hneg] at hc'
    have e1 : L.z (D.delta (-(n : Fin 5) - 1)) =
        D.x * L.z (D.delta (-(n : Fin 5))) * D.x⁻¹ := by
      calc L.z (D.delta (-(n : Fin 5) - 1))
          = D.x * (D.x⁻¹ * L.z (D.delta (-(n : Fin 5) - 1)) * D.x) * D.x⁻¹ := by group
        _ = D.x * L.z (D.delta (-(n : Fin 5))) * D.x⁻¹ := by rw [hc']
    rw [hidx, hidx2, ← hc, e1, ← ih]
    have key : L.z (D.delta 0) * (D.x⁻¹ * L.z (D.delta (n : Fin 5)) * D.x) *
        (L.z (D.delta 0))⁻¹ = (L.z (D.delta 0) * D.x⁻¹ * (L.z (D.delta 0))⁻¹) *
        (L.z (D.delta 0) * L.z (D.delta (n : Fin 5)) * (L.z (D.delta 0))⁻¹) *
        (L.z (D.delta 0) * D.x * (L.z (D.delta 0))⁻¹) := by group
    rw [ha_inv, hxa, hax] at key
    rw [key]

open Fin.NatCast Fin.CommRing in
theorem z_delta_refl (F : FanTree Γ G) (k i : Fin 5) :
    L.z (D.delta k) * L.z (D.delta i) * L.z (D.delta k) = L.z (D.delta (2 * k - i)) := by
  have hk : ((k.val : ℕ) : Fin 5) = k := Fin.cast_val_eq_self k
  have h1 : (D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val = L.z (D.delta k) := by
    have := D.zd_conj_pow k.val 0
    rwa [hk, zero_add] at this
  have h2 : (D.x ^ k.val)⁻¹ * L.z (D.delta (i - k)) * D.x ^ k.val = L.z (D.delta i) := by
    have := D.zd_conj_pow k.val (i - k)
    rwa [hk, sub_add_cancel] at this
  have h3 : L.z (D.delta 0) * L.z (D.delta (i - k)) * L.z (D.delta 0) =
      L.z (D.delta (-(i - k))) := by
    have := D.zd_refl_nat F (i - k).val
    rwa [Fin.cast_val_eq_self] at this
  have h4 : (D.x ^ k.val)⁻¹ * L.z (D.delta (-(i - k))) * D.x ^ k.val =
      L.z (D.delta (-(i - k) + k)) := by
    have := D.zd_conj_pow k.val (-(i - k))
    rwa [hk] at this
  calc L.z (D.delta k) * L.z (D.delta i) * L.z (D.delta k)
      = ((D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val) *
        ((D.x ^ k.val)⁻¹ * L.z (D.delta (i - k)) * D.x ^ k.val) *
        ((D.x ^ k.val)⁻¹ * L.z (D.delta 0) * D.x ^ k.val) := by rw [h1, h2]
    _ = (D.x ^ k.val)⁻¹ * (L.z (D.delta 0) * L.z (D.delta (i - k)) * L.z (D.delta 0)) *
        D.x ^ k.val := by group
    _ = L.z (D.delta (2 * k - i)) := by
      rw [h3, h4]
      congr 2
      ring

theorem z_delta_smul_delta (F : FanTree Γ G) (h : Fan71c F L) (k i : Fin 5) :
    L.z (D.delta k) • D.delta i = D.delta (2 * k - i) := by
  have hv := D.valence_delta F k
  apply h.z_injective (by rw [valence_smul F]; exact D.valence_delta F i) (D.valence_delta F _)
  rw [L.equivariant _ _ (D.valence_delta F i), L.z_inv hv]
  exact D.z_delta_refl F k i

theorem z_delta_smul_vert (F : FanTree Γ G) (h : Fan71c F L) (k i : Fin 5) {m : ℕ} (hm : m ≤ 4) :
    L.z (D.delta k) • (D.P i).vert m = (D.P (2 * k - i)).vert m := by
  have hz : L.z (D.delta k) • α = α :=
    MulAction.mem_stabilizer_iff.1 (D.z_delta_mem_stabilizer F h k)
  refine smul_vert_eq_of_ends F (D.P i) (D.P (2 * k - i)) _ ?_ ?_ m hm
  · rw [D.start, D.start, hz]
  · exact D.z_delta_smul_delta F h k i

end D10Set

end CFSG.Quasithin.Fan86
