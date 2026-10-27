module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem z_delta_conj_alpha (F : FanTree Γ G) (h : Fan71c F L) (k i : Fin 5) :
    L.z (D.delta k) * L.z (D.alpha i) * (L.z (D.delta k))⁻¹ = L.z (D.alpha (2 * k - i)) := by
  have := L.equivariant (L.z (D.delta k)) (D.alpha i) (D.valence_alpha F i)
  rw [← this]
  exact congrArg L.z (D.z_delta_smul_vert F h k i (m := 2) (by norm_num))

theorem prod_alpha_four (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) :
    L.z (D.alpha 2) * L.z (D.alpha 1) * L.z (D.alpha 4) * L.z (D.alpha 3) =
      L.z (D.alpha 0) := by
  have h : Fan71c F L := h7.2.2.1
  have hZ := D.isZ2Pair_alpha F h (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    (by decide)
  have hF := h81 (D.alpha 0) α (D.beta 0) (D.alpha 1) (D.alpha 2) (D.valence_alpha F 0) hZ
  set ρ : G := L.z (D.alpha 1) * L.z (D.alpha 2) with hρ
  have key : ∀ v, Γ.dist (D.alpha 0) v ≤ 4 →
      (ρ • v = v ↔ (Γ.dist α v ≤ 2 ∨ Γ.dist (D.beta 0) v ≤ 2)) := fun v hv => by
    have := Set.ext_iff.1 hF v
    exact ⟨fun hρv => this.1 ⟨hv, hρv⟩, fun hv' => (this.2 hv').2⟩
  have hα0 : ρ • D.alpha 0 = D.alpha 0 :=
    (key _ (by rw [SimpleGraph.dist_self]; norm_num)).2 (Or.inr (by
      rw [D.dist_beta_alpha 0]; norm_num))
  have hξ0 : ρ • D.xi 0 = D.xi 0 :=
    (key _ (by rw [D.dist_alpha_xi 0]; norm_num)).2 (Or.inr (by
      rw [D.dist_beta_xi F 0]))
  have hδ0 : ρ • D.delta 0 ≠ D.delta 0 := fun hfix => by
    have h1 := (key _ (by rw [D.dist_alpha_delta F 0]; norm_num)).1 hfix
    rw [D.dist_delta F 0, D.dist_beta_delta F 0] at h1
    omega
  have hξa : ρ⁻¹ • D.xi 0 = D.xi 0 := inv_smul_eq_iff.2 hξ0.symm
  have hαa : ρ⁻¹ • D.alpha 0 = D.alpha 0 := inv_smul_eq_iff.2 hα0.symm
  have hadj : Γ.Adj (D.xi 0) (ρ⁻¹ • D.delta 0) := by
    have := (F.adj_smul ρ⁻¹ (D.xi 0) (D.delta 0)).2 (D.adj_xi_delta 0)
    rwa [hξa] at this
  have hne1 : ρ⁻¹ • D.delta 0 ≠ D.delta 0 := fun h' => hδ0 (inv_smul_eq_iff.1 h').symm
  have hne2 : ρ⁻¹ • D.delta 0 ≠ D.alpha 0 := fun h' =>
    D.delta_ne_alpha 0 (MulAction.injective ρ⁻¹ (h'.trans hαa.symm))
  obtain ⟨c, hcs, hac, hdc⟩ := exists_third_neighbor (D.valence_xi F 0)
    (D.adj_alpha_xi 0).symm (D.adj_xi_delta 0) (D.delta_ne_alpha 0).symm
  have hmem : ρ⁻¹ • D.delta 0 ∈ Γ.neighborSet (D.xi 0) := hadj
  rw [hcs] at hmem
  have hc : ρ⁻¹ • D.delta 0 = c := by
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 hne2
    · exact absurd h1 hne1
    · exact h1
  have h3 := h512.2.2.1 (D.xi 0) (D.alpha 0) (D.delta 0) c (D.valence_xi F 0) hcs
    (D.delta_ne_alpha 0).symm hac hdc
  have hv0 := D.valence_delta F 0
  have hz0 : (L.z (D.delta 0))⁻¹ = L.z (D.delta 0) := L.z_inv hv0
  have hza0 : (L.z (D.alpha 0))⁻¹ = L.z (D.alpha 0) := L.z_inv (D.valence_alpha F 0)
  have hcomm0 : L.z (D.delta 0) * L.z (D.alpha 0) = L.z (D.alpha 0) * L.z (D.delta 0) :=
    h.z_comm_of_dist_le hv0 (D.valence_alpha F 0) (by
      rw [SimpleGraph.dist_comm, D.dist_alpha_delta F 0]
      norm_num)
  have hZc : L.z c = ρ⁻¹ * L.z (D.delta 0) * ρ := by
    rw [← hc, L.z_inv_smul ρ hv0]
  have E1 : ρ⁻¹ * L.z (D.delta 0) * ρ * L.z (D.delta 0) = L.z (D.alpha 0) := by
    rw [← hZc]
    have hc' : L.z c = L.z (D.delta 0) * L.z (D.alpha 0) := by
      have : L.z c = (L.z (D.alpha 0) * L.z (D.delta 0))⁻¹ := eq_inv_of_mul_eq_one_right h3
      rw [this, mul_inv_rev, hz0, hza0]
    rw [hc', mul_assoc, ← hcomm0, ← mul_assoc, L.z_mul_self hv0, one_mul]
  have hz1 : L.z (D.delta 0) * L.z (D.alpha 1) * (L.z (D.delta 0))⁻¹ = L.z (D.alpha 4) := by
    have := D.z_delta_conj_alpha F h 0 1
    rwa [show (2 * 0 - 1 : Fin 5) = 4 by decide] at this
  have hz2 : L.z (D.delta 0) * L.z (D.alpha 2) * (L.z (D.delta 0))⁻¹ = L.z (D.alpha 3) := by
    have := D.z_delta_conj_alpha F h 0 2
    rwa [show (2 * 0 - 2 : Fin 5) = 3 by decide] at this
  have E1' : ρ⁻¹ * (L.z (D.delta 0) * ρ * (L.z (D.delta 0))⁻¹) = L.z (D.alpha 0) := by
    rw [hz0]
    calc ρ⁻¹ * (L.z (D.delta 0) * ρ * L.z (D.delta 0))
        = ρ⁻¹ * L.z (D.delta 0) * ρ * L.z (D.delta 0) := by group
      _ = L.z (D.alpha 0) := E1
  have hρconj : L.z (D.delta 0) * ρ * (L.z (D.delta 0))⁻¹ =
      L.z (D.alpha 4) * L.z (D.alpha 3) := by
    rw [hρ]
    calc L.z (D.delta 0) * (L.z (D.alpha 1) * L.z (D.alpha 2)) * (L.z (D.delta 0))⁻¹
        = (L.z (D.delta 0) * L.z (D.alpha 1) * (L.z (D.delta 0))⁻¹) *
          (L.z (D.delta 0) * L.z (D.alpha 2) * (L.z (D.delta 0))⁻¹) := by group
      _ = L.z (D.alpha 4) * L.z (D.alpha 3) := by rw [hz1, hz2]
  have hρinv : ρ⁻¹ = L.z (D.alpha 2) * L.z (D.alpha 1) := by
    rw [hρ, mul_inv_rev, L.z_inv (D.valence_alpha F 1), L.z_inv (D.valence_alpha F 2)]
  calc L.z (D.alpha 2) * L.z (D.alpha 1) * L.z (D.alpha 4) * L.z (D.alpha 3)
      = ρ⁻¹ * (L.z (D.alpha 4) * L.z (D.alpha 3)) := by rw [hρinv]; group
    _ = ρ⁻¹ * (L.z (D.delta 0) * ρ * (L.z (D.delta 0))⁻¹) := by rw [hρconj]
    _ = L.z (D.alpha 0) := E1'

end D10Set

theorem fan_8_2a {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) : Fan82a F L := by
  intro α D
  have h : Fan71c F L := h7.2.2.1
  have E2 := D.prod_alpha_four F h7 h81 h512
  have hcomm : ∀ i j : Fin 5, i ≠ j →
      L.z (D.alpha i) * L.z (D.alpha j) = L.z (D.alpha j) * L.z (D.alpha i) := fun i j hij =>
    h.z_comm_of_dist_le (D.valence_alpha F i) (D.valence_alpha F j)
      (by rw [D.dist_alpha_alpha F h hij])
  show L.z (D.alpha 0) * L.z (D.alpha 1) * L.z (D.alpha 2) * L.z (D.alpha 3) *
    L.z (D.alpha 4) = 1
  calc L.z (D.alpha 0) * L.z (D.alpha 1) * L.z (D.alpha 2) * L.z (D.alpha 3) * L.z (D.alpha 4)
      = L.z (D.alpha 0) * (L.z (D.alpha 1) * L.z (D.alpha 2)) *
        (L.z (D.alpha 3) * L.z (D.alpha 4)) := by group
    _ = L.z (D.alpha 0) * (L.z (D.alpha 2) * L.z (D.alpha 1)) *
        (L.z (D.alpha 4) * L.z (D.alpha 3)) := by
      rw [hcomm 1 2 (by decide), hcomm 3 4 (by decide)]
    _ = L.z (D.alpha 0) * (L.z (D.alpha 2) * L.z (D.alpha 1) * L.z (D.alpha 4) *
        L.z (D.alpha 3)) := by group
    _ = L.z (D.alpha 0) * L.z (D.alpha 0) := by rw [E2]
    _ = 1 := L.z_mul_self (D.valence_alpha F 0)

end CFSG.Quasithin.Fan86
