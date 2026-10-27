module

public import CFSG.Quasithin.H13.GoldschmidtU43BProd

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w : G}

theorem exists_u0 (d : Swap z t w) : ∃ u : G, u ∈ Uz z ∧ u * t * u⁻¹ * t⁻¹ = z :=
  d.hyp.exists_comm_eq_z d.ht.1 d.ht.2.2.1 d.ht.2.2.2

theorem B_acts_triv [Finite G] (d : Swap z t w) {b n : G} (hb : b ∈ Bg z t) (hn : n ∈ N1g z t) :
    n⁻¹ * (b * n * b⁻¹) ∈ Vg z t := by
  have := d.comm_mem_V ((Bg z t).inv_mem (N1_le_B hn)) hb
  simpa [mul_assoc] using this

theorem conj_T_mem_B [Finite G] (d : Swap z t w) {g b : G} (hg : g ∈ Tn z t) (hb : b ∈ Bg z t) :
    g * b * g⁻¹ ∈ Bg z t := by
  have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.mp hb.1
  have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
  have hgz : g * z * g⁻¹ = z := conj_z_eq hg.1
  have hgz' : g⁻¹ * z * g = z := by
    have := conj_z_eq ((Tn z t).inv_mem hg).1
    simpa using this
  have hcases := d.hyp.conj_t_cases d.ht ((Tn z t).inv_mem hg)
  have hbc : b * (g⁻¹ * t * g) = (g⁻¹ * t * g) * b := by
    have e : g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ := by simp
    rw [e]
    rcases hcases with h1 | h1
    · rw [h1, hbt]
    · rw [h1]
      calc b * (z * t) = (b * z) * t := by group
        _ = (z * b) * t := by rw [hbz]
        _ = z * (b * t) := by group
        _ = z * (t * b) := by rw [hbt]
        _ = (z * t) * b := by group
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · calc g * b * g⁻¹ * z = g * b * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * (b * z) * g⁻¹ := by rw [hgz']; group
      _ = g * (z * b) * g⁻¹ := by rw [hbz]
      _ = (g * z * g⁻¹) * (g * b * g⁻¹) := by group
      _ = z * (g * b * g⁻¹) := by rw [hgz]
  · calc g * b * g⁻¹ * t = g * (b * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * b) * g⁻¹ := by rw [hbc]
      _ = t * (g * b * g⁻¹) := by group

theorem T_acts_triv [Finite G] (d : Swap z t w) {g n : G} (hg : g ∈ Tn z t)
    (hn : n ∈ N1g z t) : n⁻¹ * (g * n * g⁻¹) ∈ Vg z t := by
  have hp := d.cm
  rcases d.hyp.conj_t_cases d.ht hg with h1 | h1
  ·
    have hgB : g ∈ Bg z t := ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h1])⟩
    exact d.B_acts_triv hgB hn
  · obtain ⟨u, hu, hu'⟩ := d.exists_u0
    have hut : u * t * u⁻¹ = z * t := by
      calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
        _ = z * t := by rw [hu']
    have huH : u ∈ Hz z := Uz_le_Hz z hu
    have huz : u * z * u⁻¹ = z := conj_z_eq huH
    have huz' : u⁻¹ * z * u = z := by
      calc u⁻¹ * z * u = u⁻¹ * (u * z * u⁻¹) * u := by rw [huz]
        _ = z := by group
    have hut' : u⁻¹ * t * u = z * t := by
      have e1 : z * (u⁻¹ * t * u) = t := by
        calc z * (u⁻¹ * t * u) = (u⁻¹ * z * u) * (u⁻¹ * t * u) := by rw [huz']
          _ = u⁻¹ * (z * t) * u := by group
          _ = u⁻¹ * (u * t * u⁻¹) * u := by rw [hut]
          _ = t := by group
      calc u⁻¹ * t * u = z⁻¹ * (z * (u⁻¹ * t * u)) := by group
        _ = z⁻¹ * t := by rw [e1]
        _ = z * t := by rw [inv_eq_of_mul_eq_one_right d.hyp.sq_z]
    have hbB : u⁻¹ * g ∈ Bg z t := by
      refine ⟨mul_mem ((Hz z).inv_mem huH) hg.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u⁻¹ * g * t = u⁻¹ * (g * t * g⁻¹) * g := by group
        _ = u⁻¹ * (z * t) * g := by rw [h1]
        _ = (u⁻¹ * z * u) * (u⁻¹ * t * u) * u⁻¹ * g := by group
        _ = z * (z * t) * u⁻¹ * g := by rw [huz', hut']
        _ = (z * z) * t * u⁻¹ * g := by group
        _ = t * (u⁻¹ * g) := by rw [d.hyp.sq_z, one_mul]; group
    have hv₁ := d.B_acts_triv hbB hn
    have e : n⁻¹ * (g * n * g⁻¹) = (n⁻¹ * (u * n * u⁻¹)) *
        (u * (n⁻¹ * ((u⁻¹ * g) * n * (u⁻¹ * g)⁻¹)) * u⁻¹) := by group
    rw [e]
    refine mul_mem ?_ ?_
    · have := d.hyp.comm_eq ⟨n⁻¹, (Uz z).inv_mem hn.1⟩ ⟨u, hu⟩
      have e2 : n⁻¹ * (u * n * u⁻¹) = n⁻¹ * u * n⁻¹⁻¹ * u⁻¹ := by group
      rw [e2]
      rw [this]
      exact zp_z_mem z t _
    · exact hp.conj_mem_of_mem (g := u) (by rw [huz]; exact z_mem_Vg z t)
        (by rw [hut]; exact (hp.mem_Vg_iff₄ _).2 (Or.inr (Or.inr (Or.inr rfl)))) hv₁

end Swap

end CFSG.Quasithin.H13.U43
