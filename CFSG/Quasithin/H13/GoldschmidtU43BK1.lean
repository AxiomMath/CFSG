module

public import CFSG.Quasithin.H13.GoldschmidtU43BCrd
public import CFSG.Quasithin.H13.GoldschmidtU43BReach
public import CFSG.Quasithin.H13.GoldschmidtU43BElemN

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w a : G}

@[expose] def gE (z t w a : G) : Fin 4 → G := ![z, t, a, w⁻¹ * a * w]

theorem comm4_gE [Finite G] (s : Swap z t w) (ha : Good z t a) : Comm4 (gE z t w a) := by
  have hB := s.m_mem_B ha
  have hz : (w⁻¹ * a * w) * z = z * (w⁻¹ * a * w) :=
    Subgroup.mem_centralizer_singleton_iff.mp hB.1
  have ht : (w⁻¹ * a * w) * t = t * (w⁻¹ * a * w) :=
    Subgroup.mem_centralizer_singleton_iff.mp hB.2
  have hat : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp ha.mem.2
  exact comm4_mk s.cm.sq_z s.cm.sq_t ha.sq (m_sq ha) s.cm.comm (s.hyp.z_comm ha.mem.1)
    hz.symm hat.symm ht.symm (s.a_comm_m ha)

theorem crd_gE_mem (c : V4) : crd (gE z t w a) c ∈ Eg z t w a := by
  have hzp : ∀ (x : G), x ∈ Eg z t w a → ∀ b : ZMod 2, zp x b ∈ Eg z t w a := by
    intro x hx b
    rcases zmod_two_cases b with rfl | rfl
    · rw [zp_zero]; exact one_mem _
    · rw [zp_one]; exact hx
  unfold crd
  simp only [gE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  exact mul_mem (mul_mem (mul_mem (hzp _ z_mem_Eg _) (hzp _ t_mem_Eg _)) (hzp _ a_mem_Eg _))
    (hzp _ m_mem_Eg _)

theorem exists_crd [Finite G] (s : Swap z t w) (ha : Good z t a) {y : G} (hy : y ∈ Eg z t w a) :
    ∃ c : V4, y = crd (gE z t w a) c := by
  obtain ⟨v, hv, i, j, rfl⟩ := (s.mem_Eg_iff ha y).1 hy
  obtain ⟨c0, c1, rfl⟩ := (s.cm.mem_Vg_iff v).1 hv
  refine ⟨![c0, c1, i, j], ?_⟩
  simp [crd, gE]

theorem crd_gE_indep [Finite G] (s : Swap z t w) (ha : Good z t a) {c : V4}
    (h : crd (gE z t w a) c = 1) : c = 0 := by
  have hv : zp z (c 0) * zp t (c 1) ∈ Vg z t :=
    (s.cm.mem_Vg_iff _).2 ⟨c 0, c 1, rfl⟩
  have h1 : zp z (c 0) * zp t (c 1) * zp a (c 2) * zp (w⁻¹ * a * w) (c 3) =
      1 * zp a 0 * zp (w⁻¹ * a * w) 0 := by
    rw [zp_zero, zp_zero, one_mul, mul_one]
    simpa [crd, gE] using h
  obtain ⟨e1, e2, e3⟩ := s.Eg_inj ha hv (one_mem _) h1
  have hz1 := s.hyp.z_ne_one
  have ht1 := s.ht.2.2.1
  have hzt : z * t ≠ 1 := fun e => s.ht.2.2.2 (by
    calc t = z⁻¹ * (z * t) := by group
      _ = z⁻¹ := by rw [e, mul_one]
      _ = z := inv_eq_of_mul_eq_one_right s.hyp.sq_z)
  have hc01 : c 0 = 0 ∧ c 1 = 0 := by
    rcases zmod_two_cases (c 0) with h0 | h0 <;> rcases zmod_two_cases (c 1) with h1' | h1'
    · exact ⟨h0, h1'⟩
    · exfalso; rw [h0, h1', zp_zero, zp_one, one_mul] at e1; exact ht1 e1
    · exfalso; rw [h0, h1', zp_zero, zp_one, mul_one] at e1; exact hz1 e1
    · exfalso; rw [h0, h1', zp_one, zp_one] at e1; exact hzt e1
  funext i
  fin_cases i
  · exact hc01.1
  · exact hc01.2
  · exact e2
  · exact e3

theorem exists_Wm [Finite G] (s : Swap z t w) (ha : Good z t a) :
    ∃ x y : ZMod 2, ∀ i : Fin 4,
      w * gE z t w a i * w⁻¹ = crd (gE z t w a) (Wm x y i) := by
  have hB := s.m_mem_B ha
  have hc : (w * w) * (w⁻¹ * a * w) * (w * w)⁻¹ * (w⁻¹ * a * w)⁻¹ ∈ Vg z t :=
    s.comm_mem_V s.w_sq_mem_B hB
  obtain ⟨x, y, hxy⟩ := (s.cm.mem_Vg_iff _).1 hc
  refine ⟨x, y, fun i => ?_⟩
  have hwa : w * a * w⁻¹ = (zp z x * zp t y) * (w⁻¹ * a * w) := by
    rw [← hxy]; group
  fin_cases i
  · show w * z * w⁻¹ = crd (gE z t w a) (idc 1)
    rw [crd_idc]
    exact s.w1'
  · show w * t * w⁻¹ = crd (gE z t w a) (idc 0)
    rw [crd_idc]
    exact s.w2'
  · show w * a * w⁻¹ = crd (gE z t w a) ![x, y, 0, 1]
    rw [hwa]
    simp [crd, gE, zp_zero, zp_one]
  · show w * (w⁻¹ * a * w) * w⁻¹ = crd (gE z t w a) (idc 2)
    rw [crd_idc]
    show _ = a
    group

theorem exists_Um [Finite G] (s : Swap z t w) (ha : Good z t a) {u : G} (hu : u ∈ Uz z)
    (hut : u * t * u⁻¹ = z * t) :
    ∃ ε x y : ZMod 2, ∀ i : Fin 4,
      u * gE z t w a i * u⁻¹ = crd (gE z t w a) (Um ε x y i) := by
  have h := s.hyp
  obtain ⟨huz, -, -, -⟩ := s.u_facts hu hut
  have hcomm := h.comm_eq ⟨u, hu⟩ ⟨a, ha.mem.1⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ZMod 2, u * a * u⁻¹ * a⁻¹ = zp z ε := ⟨_, hcomm⟩
  have hua : u * a * u⁻¹ = zp z ε * a := by
    calc u * a * u⁻¹ = (u * a * u⁻¹ * a⁻¹) * a := by group
      _ = zp z ε * a := by rw [hε]
  obtain ⟨hn'N, hX⟩ := s.key_B hu hut ha.mem
  obtain ⟨x, y, hxy⟩ := (s.cm.mem_Vg_iff _).1 ((Vg z t).inv_mem hX)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.sq
  have hn' : (w⁻¹ * a * w)⁻¹ * (u * (w⁻¹ * a * w) * u⁻¹) = (zp z x * zp t y) * a := by
    have e : (w⁻¹ * a * w)⁻¹ * (u * (w⁻¹ * a * w) * u⁻¹) * a⁻¹ = zp z x * zp t y := by
      rw [← hxy]; group
    rw [hainv] at e
    calc (w⁻¹ * a * w)⁻¹ * (u * (w⁻¹ * a * w) * u⁻¹)
        = ((w⁻¹ * a * w)⁻¹ * (u * (w⁻¹ * a * w) * u⁻¹) * a) * a := by
          rw [mul_assoc _ a a, ha.sq, mul_one]
      _ = (zp z x * zp t y) * a := by rw [e]
  have hv0 : zp z x * zp t y ∈ Vg z t := (s.cm.mem_Vg_iff _).2 ⟨x, y, rfl⟩
  have hum : u * (w⁻¹ * a * w) * u⁻¹ = (zp z x * zp t y) * a * (w⁻¹ * a * w) := by
    have e1 : u * (w⁻¹ * a * w) * u⁻¹ = (w⁻¹ * a * w) * ((zp z x * zp t y) * a) := by
      rw [← hn']; group
    rw [e1]
    have hc1 := s.V_central (s.m_mem_B ha) hv0
    calc (w⁻¹ * a * w) * ((zp z x * zp t y) * a)
        = ((w⁻¹ * a * w) * (zp z x * zp t y)) * a := by group
      _ = ((zp z x * zp t y) * (w⁻¹ * a * w)) * a := by rw [hc1]
      _ = (zp z x * zp t y) * ((w⁻¹ * a * w) * a) := by group
      _ = (zp z x * zp t y) * (a * (w⁻¹ * a * w)) := by rw [← s.a_comm_m ha]
      _ = _ := by group
  refine ⟨ε, x, y, fun i => ?_⟩
  fin_cases i
  · show u * z * u⁻¹ = crd (gE z t w a) (idc 0)
    rw [crd_idc]
    exact huz
  · show u * t * u⁻¹ = crd (gE z t w a) (idc 0 + idc 1)
    rw [(s.comm4_gE ha).crd_add, crd_idc, crd_idc]
    exact hut
  · show u * a * u⁻¹ = crd (gE z t w a) ![ε, 0, 1, 0]
    rw [hua]
    simp [crd, gE, zp_zero, zp_one]
  · show u * (w⁻¹ * a * w) * u⁻¹ = crd (gE z t w a) ![x, y, 1, 1]
    rw [hum]
    simp [crd, gE, zp_one]

end Swap

end CFSG.Quasithin.H13.U43
