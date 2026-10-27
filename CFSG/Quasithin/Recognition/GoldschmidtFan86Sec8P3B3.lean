module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T
open Fin.NatCast Fin.CommRing

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem isW1Elem_smul_vert (F : FanTree Γ G) (h71c : Fan71c F L) {w : G} (hw : IsW1Elem D w)
    (i : Fin 5) {m : ℕ} (hm : m ≤ 4) : w⁻¹ • (D.P i).vert m = (D.P (2 * i)).vert m := by
  obtain ⟨hP, -, hwx, -⟩ := hw
  have hwα : w • α = α := by
    have := (Arc.mem_stab G).1 hP 0 (by norm_num)
    rwa [D.start] at this
  have hwδ : w • D.delta 0 = D.delta 0 := (Arc.mem_stab G).1 hP 4 (by norm_num)
  have hwz : w⁻¹ * L.z (D.delta 0) * w = L.z (D.delta 0) := by
    have h1 := L.z_inv_smul w (D.valence_delta F 0)
    rw [inv_smul_eq_iff.2 hwδ.symm] at h1
    exact h1.symm
  have hxn : w⁻¹ * D.x ^ i.val * w = D.x ^ (2 * i.val) := by
    have h1 := conj_pow (a := w⁻¹) (b := D.x) (i := i.val)
    rw [inv_inv, hwx, ← pow_mul] at h1
    exact h1.symm
  have hlab : L.z (w⁻¹ • D.delta i) = L.z (D.delta (2 * i)) := by
    rw [L.z_inv_smul w (D.valence_delta F i)]
    have h1 : L.z (D.delta i) = (D.x ^ i.val)⁻¹ * L.z (D.delta 0) * D.x ^ i.val := by
      have := D.zd_conj_pow i.val 0
      rw [Fin.cast_val_eq_self, zero_add] at this
      exact this.symm
    have h2 : L.z (D.delta (2 * i)) = (D.x ^ (2 * i.val))⁻¹ * L.z (D.delta 0) *
        D.x ^ (2 * i.val) := by
      have := D.zd_conj_pow (2 * i.val) 0
      have e : ((2 * i.val : ℕ) : Fin 5) = 2 * i := by
        push_cast
        rfl
      rw [zero_add, e] at this
      exact this.symm
    rw [h1, h2, ← hxn]
    calc w⁻¹ * ((D.x ^ i.val)⁻¹ * L.z (D.delta 0) * D.x ^ i.val) * w
        = (w⁻¹ * D.x ^ i.val * w)⁻¹ * (w⁻¹ * L.z (D.delta 0) * w) * (w⁻¹ * D.x ^ i.val * w) := by
          group
      _ = (w⁻¹ * D.x ^ i.val * w)⁻¹ * L.z (D.delta 0) * (w⁻¹ * D.x ^ i.val * w) := by rw [hwz]
  have hδi : w⁻¹ • D.delta i = D.delta (2 * i) :=
    h71c.z_injective (by rw [valence_smul F]; exact D.valence_delta F i) (D.valence_delta F _) hlab
  refine smul_vert_eq_of_ends F (D.P i) (D.P (2 * i)) w⁻¹ ?_ ?_ m hm
  · rw [D.start, D.start]
    exact inv_smul_eq_iff.2 hwα.symm
  · exact hδi

end Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_6b (F : FanTree Γ G) (L : ZLab Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h75 : Fan75 F L) (h65 : Fan65 F) (h84a : Fan84a F L) : Fan86b F L := by
  intro α D
  refine ⟨Sec8P3.exists_w1 D F h71a h71c h75 h65 (h84a α D).1 (h84a α D).2,
    fun w hw i m hm => ?_⟩
  exact Sec8P3.isW1Elem_smul_vert D F h71c hw i hm

end CFSG.Quasithin.Fan86
