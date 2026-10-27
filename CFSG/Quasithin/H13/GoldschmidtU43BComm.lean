module

public import CFSG.Quasithin.H13.GoldschmidtU43BKey

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w : G}

theorem zt_mem_Vg (z t : G) : z * t ∈ Vg z t := mul_mem (z_mem_Vg z t) (t_mem_Vg z t)

theorem w_zt (d : Swap z t w) : w * (z * t) * w⁻¹ = z * t := by
  calc w * (z * t) * w⁻¹ = (w * z * w⁻¹) * (w * t * w⁻¹) := by group
    _ = t * z := by rw [d.w1', d.w2']
    _ = z * t := d.cm.comm.symm

theorem u_facts (d : Swap z t w) {u : G} (hu : u ∈ Uz z) (hut : u * t * u⁻¹ = z * t) :
    u * z * u⁻¹ = z ∧ u⁻¹ * z * u = z ∧ u⁻¹ * t * u = z * t ∧ u⁻¹ * (z * t) * u = t := by
  have huz : u * z * u⁻¹ = z := conj_z_eq (Uz_le_Hz z hu)
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
  refine ⟨huz, huz', hut', ?_⟩
  calc u⁻¹ * (z * t) * u = (u⁻¹ * z * u) * (u⁻¹ * t * u) := by group
    _ = z * (z * t) := by rw [huz', hut']
    _ = (z * z) * t := by group
    _ = t := by rw [d.hyp.sq_z, one_mul]

theorem key_A [Finite G] (d : Swap z t w) {u : G} (hu : u ∈ Uz z) (hut : u * t * u⁻¹ = z * t)
    {n : G} (hn : n ∈ N1g z t) :
    ∃ v ∈ Vg z t, w * (u * (w⁻¹ * n * w) * u⁻¹) * w⁻¹ = (u * (w⁻¹ * n * w) * u⁻¹) * v := by
  have hp := d.cm
  obtain ⟨huz, huz', hut', huzt⟩ := d.u_facts hu hut
  have hwzt := d.w_zt
  have hs_z : (w * u⁻¹ * w * u * w⁻¹) * z * (w * u⁻¹ * w * u * w⁻¹)⁻¹ = z := by
    calc (w * u⁻¹ * w * u * w⁻¹) * z * (w * u⁻¹ * w * u * w⁻¹)⁻¹
        = w * (u⁻¹ * (w * (u * (w⁻¹ * z * w) * u⁻¹) * w⁻¹) * u) * w⁻¹ := by group
      _ = w * (u⁻¹ * (w * (u * t * u⁻¹) * w⁻¹) * u) * w⁻¹ := by rw [d.w1]
      _ = w * (u⁻¹ * (w * (z * t) * w⁻¹) * u) * w⁻¹ := by rw [hut]
      _ = w * (u⁻¹ * (z * t) * u) * w⁻¹ := by rw [hwzt]
      _ = w * t * w⁻¹ := by rw [huzt]
      _ = z := d.w2'
  have hs_t : (w * u⁻¹ * w * u * w⁻¹) * t * (w * u⁻¹ * w * u * w⁻¹)⁻¹ = z * t := by
    calc (w * u⁻¹ * w * u * w⁻¹) * t * (w * u⁻¹ * w * u * w⁻¹)⁻¹
        = w * (u⁻¹ * (w * (u * (w⁻¹ * t * w) * u⁻¹) * w⁻¹) * u) * w⁻¹ := by group
      _ = w * (u⁻¹ * (w * (u * z * u⁻¹) * w⁻¹) * u) * w⁻¹ := by rw [d.w2]
      _ = w * (u⁻¹ * (w * z * w⁻¹) * u) * w⁻¹ := by rw [huz]
      _ = w * (u⁻¹ * t * u) * w⁻¹ := by rw [d.w1']
      _ = w * (z * t) * w⁻¹ := by rw [hut']
      _ = z * t := hwzt
  have hsH : (w * u⁻¹ * w * u * w⁻¹) ∈ Hz z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (w * u⁻¹ * w * u * w⁻¹) * z = ((w * u⁻¹ * w * u * w⁻¹) * z * (w * u⁻¹ * w * u * w⁻¹)⁻¹)
          * (w * u⁻¹ * w * u * w⁻¹) := by group
      _ = z * (w * u⁻¹ * w * u * w⁻¹) := by rw [hs_z]
  have hsT : (w * u⁻¹ * w * u * w⁻¹) ∈ Tn z t :=
    d.hyp.mem_Tn_of d.ht hsH (by rw [hs_t]; exact zt_mem_Vg z t)
  have hv₀ := d.T_acts_triv hsT hn
  refine ⟨(u * w⁻¹) * (n⁻¹ * ((w * u⁻¹ * w * u * w⁻¹) * n * (w * u⁻¹ * w * u * w⁻¹)⁻¹)) *
      (u * w⁻¹)⁻¹, hp.conj_mem_of_mem (g := u * w⁻¹) ?_ ?_ hv₀, ?_⟩
  · have e : u * w⁻¹ * z * (u * w⁻¹)⁻¹ = z * t := by
      calc u * w⁻¹ * z * (u * w⁻¹)⁻¹ = u * (w⁻¹ * z * w) * u⁻¹ := by group
        _ = z * t := by rw [d.w1, hut]
    rw [e]
    exact zt_mem_Vg z t
  · have e : u * w⁻¹ * t * (u * w⁻¹)⁻¹ = z := by
      calc u * w⁻¹ * t * (u * w⁻¹)⁻¹ = u * (w⁻¹ * t * w) * u⁻¹ := by group
        _ = z := by rw [d.w2, huz]
    rw [e]
    exact z_mem_Vg z t
  · group

theorem Vg_le_N2 (d : Swap z t w) {x : G} (hx : x ∈ Vg z t) : x ∈ N2g z t w :=
  ((d.mem_N1_inf_N2 x).2 hx).2

theorem Vg_le_N1 (d : Swap z t w) {x : G} (hx : x ∈ Vg z t) : x ∈ N1g z t :=
  ((d.mem_N1_inf_N2 x).2 hx).1

theorem key_B [Finite G] (d : Swap z t w) {u : G} (hu : u ∈ Uz z) (hut : u * t * u⁻¹ = z * t)
    {n : G} (hn : n ∈ N1g z t) :
    (w⁻¹ * n * w)⁻¹ * (u * (w⁻¹ * n * w) * u⁻¹) ∈ N1g z t ∧
      n * ((w⁻¹ * n * w)⁻¹ * (u * (w⁻¹ * n * w) * u⁻¹))⁻¹ ∈ Vg z t := by
  have hp := d.cm
  have huH : u ∈ Hz z := Uz_le_Hz z hu
  have huT : u ∈ Tn z t :=
    d.hyp.mem_Tn_of d.ht huH (by rw [hut]; exact zt_mem_Vg z t)
  have hmN2 : (w⁻¹ * n * w) ∈ N2g z t w := by
    rw [mem_N2]
    have e : w * (w⁻¹ * n * w) * w⁻¹ = n := by group
    rw [e]
    exact hn
  obtain ⟨v, hv, hAe⟩ := d.key_A hu hut hn
  obtain ⟨m, hm⟩ : ∃ m, m = w⁻¹ * n * w := ⟨_, rfl⟩
  rw [← hm] at hmN2 hAe ⊢
  have hmB : m ∈ Bg z t := d.N2_le_B hmN2
  have heB : u * m * u⁻¹ ∈ Bg z t := d.conj_T_mem_B huT hmB
  have hn'B : m⁻¹ * (u * m * u⁻¹) ∈ Bg z t := mul_mem ((Bg z t).inv_mem hmB) heB
  have hn'U : m⁻¹ * (u * m * u⁻¹) ∈ Uz z := by
    have h1 : m⁻¹ * u * m ∈ Uz z := by
      have := (Subgroup.mem_normalizer_iff.mp
        (Hz_le_normalizer z ((Hz z).inv_mem hmB.1)) u).mp hu
      simpa using this
    have e : m⁻¹ * (u * m * u⁻¹) = (m⁻¹ * u * m) * u⁻¹ := by group
    rw [e]
    exact mul_mem h1 ((Uz z).inv_mem hu)
  have hn'N : m⁻¹ * (u * m * u⁻¹) ∈ N1g z t := ⟨hn'U, hn'B.2⟩
  refine ⟨hn'N, ?_⟩
  obtain ⟨n', hn'⟩ : ∃ n', n' = m⁻¹ * (u * m * u⁻¹) := ⟨_, rfl⟩
  rw [← hn'] at hn'N ⊢
  have hn'B' : n' ∈ Bg z t := N1_le_B hn'N
  have hnB : n ∈ Bg z t := N1_le_B hn
  have hem : u * m * u⁻¹ = m * n' := by rw [hn']; group
  have hn''N2 : w * n' * w⁻¹ ∈ N2g z t w := by
    rw [mem_N2]
    have e : w * (w * n' * w⁻¹) * w⁻¹ = (w * w) * n' * (w * w)⁻¹ := by group
    rw [e]
    exact N1_normal d.w_sq_mem_B hn'N
  have hn''B : w * n' * w⁻¹ ∈ Bg z t := d.N2_le_B hn''N2
  have hwe : w * (u * m * u⁻¹) * w⁻¹ = n * (w * n' * w⁻¹) := by
    rw [hem]
    calc w * (m * n') * w⁻¹ = (w * m * w⁻¹) * (w * n' * w⁻¹) := by group
      _ = n * (w * n' * w⁻¹) := by rw [hm]; congr 1; group
  have hE1 : n = m * n' * v * (w * n' * w⁻¹)⁻¹ := by
    have h1 : n * (w * n' * w⁻¹) = m * n' * v := by rw [← hwe, hAe, hem]
    calc n = (n * (w * n' * w⁻¹)) * (w * n' * w⁻¹)⁻¹ := by group
      _ = m * n' * v * (w * n' * w⁻¹)⁻¹ := by rw [h1]
  have hcen : v * ((w * n' * w⁻¹)⁻¹ * n'⁻¹) = ((w * n' * w⁻¹)⁻¹ * n'⁻¹) * v :=
    (d.V_central (mul_mem ((Bg z t).inv_mem hn''B) ((Bg z t).inv_mem hn'B')) hv).symm
  have hX : n * n'⁻¹ = (m * (w * n' * w⁻¹)⁻¹) *
      (((w * n' * w⁻¹) * n' * (w * n' * w⁻¹)⁻¹ * n'⁻¹) * v) := by
    calc n * n'⁻¹ = (m * n' * v * (w * n' * w⁻¹)⁻¹) * n'⁻¹ := by rw [← hE1]
      _ = m * n' * (v * ((w * n' * w⁻¹)⁻¹ * n'⁻¹)) := by group
      _ = m * n' * (((w * n' * w⁻¹)⁻¹ * n'⁻¹) * v) := by rw [hcen]
      _ = (m * (w * n' * w⁻¹)⁻¹) *
          (((w * n' * w⁻¹) * n' * (w * n' * w⁻¹)⁻¹ * n'⁻¹) * v) := by group
  have hk := d.comm_mem_V hn''B hn'B'
  have hX2 : n * n'⁻¹ ∈ N2g z t w := by
    rw [hX]
    exact mul_mem (mul_mem hmN2 ((N2g z t w).inv_mem hn''N2))
      (d.Vg_le_N2 (mul_mem hk hv))
  have hX1 : n * n'⁻¹ ∈ N1g z t := mul_mem hn ((N1g z t).inv_mem hn'N)
  exact (d.mem_N1_inf_N2 _).1 ⟨hX1, hX2⟩

end Swap

end CFSG.Quasithin.H13.U43
