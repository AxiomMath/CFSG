module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Ord

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2K

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem mem_ballStab_smul_iff (F : FanTree Γ G) (n : ℕ) (g : G) (a : V) {h : G} :
    h ∈ ballStab Γ G n (g • a) ↔ g⁻¹ * h * g ∈ ballStab Γ G n a := by
  rw [mem_ballStab, mem_ballStab]
  constructor
  · intro H w hw
    have h1 := H (g • w) (by rw [dist_smul F]; exact hw)
    calc (g⁻¹ * h * g) • w = g⁻¹ • (h • (g • w)) := by simp [mul_smul]
      _ = w := by rw [h1, inv_smul_smul]
  · intro H w hw
    have h1 := H (g⁻¹ • w) (by
      have := dist_smul F g⁻¹ (g • a) w
      rw [inv_smul_smul] at this
      rw [this]
      exact hw)
    have h2 : g⁻¹ • (h • w) = g⁻¹ • w := by
      calc g⁻¹ • (h • w) = g⁻¹ • (h • (g • (g⁻¹ • w))) := by rw [smul_inv_smul]
        _ = (g⁻¹ * h * g) • (g⁻¹ • w) := by simp [mul_smul]
        _ = g⁻¹ • w := h1
    exact MulAction.injective g⁻¹ h2

theorem exists_nbr_dist_le (F : FanTree Γ G) {a v : V} {n : ℕ} (h : Γ.dist a v ≤ n + 1)
    (hv : v ≠ a) : ∃ b, Γ.Adj a b ∧ Γ.dist b v ≤ n := by
  have hpos : 0 < Γ.dist a v := F.isTree.connected.pos_dist_of_ne (Ne.symm hv)
  have hcomm : Γ.dist v a = Γ.dist a v := SimpleGraph.dist_comm
  obtain ⟨w, hwa, hw⟩ := IsTree.exists_adj_dist_succ F.isTree (u := v) (v := a)
    (n := Γ.dist v a - 1) (by omega)
  refine ⟨w, hwa.symm, ?_⟩
  have hcomm' : Γ.dist w v = Γ.dist v w := SimpleGraph.dist_comm
  omega

theorem conj_mem_nbrStab (F : FanTree Γ G) {a : V} {s u : G} (hsa : s • a = a) (hs2 : s * s = 1)
    (hu : u ∈ nbrStab Γ G a) : s * u * s ∈ nbrStab Γ G a := by
  rw [mem_nbrStab] at hu ⊢
  intro w hw
  have hsw : Γ.Adj a (s • w) := by
    have := (F.adj_smul s a w).2 hw
    rwa [hsa] at this
  calc (s * u * s) • w = s • (u • (s • w)) := by simp [mul_smul]
    _ = s • (s • w) := by rw [hu _ hsw]
    _ = w := by rw [← mul_smul, hs2, one_smul]

open Fin.NatCast in
theorem x_pow_inv_smul_beta (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 5) :
    (D.x ^ j.val)⁻¹ • D.beta 0 = D.beta j := by
  have hj : ((j.val : ℕ) : Fin 5) = j := Fin.cast_val_eq_self j
  have := D.x_pow_inv_smul_vert F h71c j.val 0 (m := 1) (by norm_num)
  rw [hj, zero_add] at this
  exact this

end Sec8P2K

end CFSG.Quasithin.Fan86
