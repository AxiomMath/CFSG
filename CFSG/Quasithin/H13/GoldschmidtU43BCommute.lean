module

public import CFSG.Quasithin.H13.GoldschmidtU43BComm

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w : G}

theorem commute_conj [Finite G] (d : Swap z t w) {n : G} (hn : n ∈ N1g z t) :
    n * (w⁻¹ * n * w) = (w⁻¹ * n * w) * n := by
  have hp := d.cm
  obtain ⟨u, hu, hu'⟩ := d.exists_u0
  have hut : u * t * u⁻¹ = z * t := by
    calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
      _ = z * t := by rw [hu']
  obtain ⟨huz, huz', hut', huzt⟩ := d.u_facts hu hut
  have huT : u ∈ Tn z t :=
    d.hyp.mem_Tn_of d.ht (Uz_le_Hz z hu) (by rw [hut]; exact zt_mem_Vg z t)
  obtain ⟨hn'N, hX⟩ := d.key_B hu hut hn
  have hmN2 : (w⁻¹ * n * w) ∈ N2g z t w := by
    rw [mem_N2]
    have e : w * (w⁻¹ * n * w) * w⁻¹ = n := by group
    rw [e]
    exact hn
  obtain ⟨m, hm⟩ : ∃ m, m = w⁻¹ * n * w := ⟨_, rfl⟩
  rw [← hm] at hmN2 hn'N hX ⊢
  have hmB : m ∈ Bg z t := d.N2_le_B hmN2
  have hnB : n ∈ Bg z t := N1_le_B hn
  obtain ⟨n', hn'⟩ : ∃ n', n' = m⁻¹ * (u * m * u⁻¹) := ⟨_, rfl⟩
  rw [← hn'] at hn'N hX
  have hn'B : n' ∈ Bg z t := N1_le_B hn'N
  have hem : u * m * u⁻¹ = m * n' := by rw [hn']; group
  have hnn' : n * n' = n' * n := by
    have hx := d.V_central hn'B hX
    calc n * n' = (n * n'⁻¹) * n' * n' := by group
      _ = n' * (n * n'⁻¹) * n' := by rw [← hx]
      _ = n' * n := by group
  have hnn'' : n' * n⁻¹ = n⁻¹ * n' := by
    calc n' * n⁻¹ = n⁻¹ * (n * n') * n⁻¹ := by group
      _ = n⁻¹ * (n' * n) * n⁻¹ := by rw [hnn']
      _ = n⁻¹ * n' := by group
  have hcm : n * m * n⁻¹ * m⁻¹ ∈ Vg z t := d.comm_mem_V hnB hmB
  have h1 : n * (u * m * u⁻¹) * n⁻¹ * (u * m * u⁻¹)⁻¹ = n * m * n⁻¹ * m⁻¹ := by
    rw [hem]
    calc n * (m * n') * n⁻¹ * (m * n')⁻¹ = n * m * (n' * n⁻¹) * n'⁻¹ * m⁻¹ := by group
      _ = n * m * (n⁻¹ * n') * n'⁻¹ * m⁻¹ := by rw [hnn'']
      _ = n * m * n⁻¹ * m⁻¹ := by group
  have hv₂ : n⁻¹ * (u⁻¹ * n * u) ∈ Vg z t := by
    have := d.T_acts_triv ((Tn z t).inv_mem huT) hn
    simpa using this
  have hv₂c : (n⁻¹ * (u⁻¹ * n * u)) * m = m * (n⁻¹ * (u⁻¹ * n * u)) :=
    (d.V_central hmB hv₂).symm
  have h2 : n * (u * m * u⁻¹) * n⁻¹ * (u * m * u⁻¹)⁻¹ = u * (n * m * n⁻¹ * m⁻¹) * u⁻¹ := by
    have e1 : u⁻¹ * n * u = n * (n⁻¹ * (u⁻¹ * n * u)) := by group
    calc n * (u * m * u⁻¹) * n⁻¹ * (u * m * u⁻¹)⁻¹
        = u * ((u⁻¹ * n * u) * m * (u⁻¹ * n * u)⁻¹ * m⁻¹) * u⁻¹ := by group
      _ = u * ((n * (n⁻¹ * (u⁻¹ * n * u))) * m * (n * (n⁻¹ * (u⁻¹ * n * u)))⁻¹ * m⁻¹) * u⁻¹ := by
          rw [← e1]
      _ = u * (n * ((n⁻¹ * (u⁻¹ * n * u)) * m * (n⁻¹ * (u⁻¹ * n * u))⁻¹) * n⁻¹ * m⁻¹) * u⁻¹ := by
          group
      _ = u * (n * m * n⁻¹ * m⁻¹) * u⁻¹ := by
          rw [hv₂c]; group
  have hcu : u * (n * m * n⁻¹ * m⁻¹) * u⁻¹ = n * m * n⁻¹ * m⁻¹ := by rw [← h2, h1]
  have hcz : n * m * n⁻¹ * m⁻¹ = 1 ∨ n * m * n⁻¹ * m⁻¹ = z := by
    have hzne : z ≠ 1 := d.hyp.z_ne_one
    rcases (hp.mem_Vg_iff₄ _).1 hcm with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso
      rw [e, hut] at hcu
      apply hzne
      calc z = (z * t) * t⁻¹ := by group
        _ = t * t⁻¹ := by rw [hcu]
        _ = 1 := by group
    · exfalso
      rw [e] at hcu
      have : u * (z * t) * u⁻¹ = t := by
        calc u * (z * t) * u⁻¹ = (u * z * u⁻¹) * (u * t * u⁻¹) := by group
          _ = z * (z * t) := by rw [huz, hut]
          _ = t := by rw [← mul_assoc, d.hyp.sq_z, one_mul]
      rw [this] at hcu
      apply hzne
      calc z = (z * t) * t⁻¹ := by group
        _ = t * t⁻¹ := by rw [← hcu]
        _ = 1 := by group
  have hv₃ : n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹) ∈ Vg z t :=
    d.B_acts_triv ((Bg z t).inv_mem d.w_sq_mem_B) hn
  have hv₃c : (n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹)) * m⁻¹ =
      m⁻¹ * (n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹)) :=
    (d.V_central ((Bg z t).inv_mem hmB) hv₃).symm
  have hsw : w⁻¹ * (n * m * n⁻¹ * m⁻¹) * w = (n * m * n⁻¹ * m⁻¹)⁻¹ := by
    have e1 : w⁻¹ * m * w = n * (n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹)) := by
      rw [hm]; simp only [mul_inv_rev, inv_inv]; group
    calc w⁻¹ * (n * m * n⁻¹ * m⁻¹) * w
        = (w⁻¹ * n * w) * (w⁻¹ * m * w) * (w⁻¹ * n * w)⁻¹ * (w⁻¹ * m * w)⁻¹ := by group
      _ = m * (n * (n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹))) * m⁻¹ *
          (n * (n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹)))⁻¹ := by rw [← hm, e1]
      _ = m * n * ((n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹)) * m⁻¹ *
          (n⁻¹ * ((w * w)⁻¹ * n * (w * w)⁻¹⁻¹))⁻¹) * n⁻¹ := by group
      _ = m * n * m⁻¹ * n⁻¹ := by rw [hv₃c]; group
      _ = (n * m * n⁻¹ * m⁻¹)⁻¹ := by group
  rcases hcz with e | e
  · have : n * m * n⁻¹ * m⁻¹ = 1 := e
    calc n * m = (n * m * n⁻¹ * m⁻¹) * m * n := by group
      _ = m * n := by rw [this]; group
  · exfalso
    rw [e] at hsw
    rw [d.w1, inv_eq_of_mul_eq_one_right d.hyp.sq_z] at hsw
    exact d.ht.2.2.2 hsw

end Swap

end CFSG.Quasithin.H13.U43
