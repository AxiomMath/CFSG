module

public import CFSG.Quasithin.H13.GoldschmidtU43BElem

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w a : G}

theorem z_mem_Eg : z ∈ Eg z t w a := Subgroup.subset_closure (by simp)

theorem t_mem_Eg : t ∈ Eg z t w a := Subgroup.subset_closure (by simp)

theorem a_mem_Eg : a ∈ Eg z t w a := Subgroup.subset_closure (by simp)

theorem m_mem_Eg : w⁻¹ * a * w ∈ Eg z t w a := Subgroup.subset_closure (by simp)

theorem B_conj_Eg [Finite G] (s : Swap z t w) (ha : Good z t a) {b : G} (hb : b ∈ Bg z t)
    {x : G} (hx : x ∈ Eg z t w a) : b * x * b⁻¹ ∈ Eg z t w a := by
  have key : ∀ y ∈ Bg z t, y ∈ Eg z t w a → b * y * b⁻¹ ∈ Eg z t w a := by
    intro y hyB hyE
    have e : b * y * b⁻¹ = (b * y * b⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact mul_mem (V_le_Eg (s.comm_mem_V hb hyB)) hyE
  refine conj_mem_closure (fun y hy => ?_) hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with h | h | h | h <;> rw [h]
  · exact key z (N1_le_B (s.Vg_le_N1 (z_mem_Vg z t))) z_mem_Eg
  · exact key t (N1_le_B (s.Vg_le_N1 (t_mem_Vg z t))) t_mem_Eg
  · exact key a (N1_le_B ha.mem) a_mem_Eg
  · exact key (w⁻¹ * a * w) (s.m_mem_B ha) m_mem_Eg

theorem u_conj_Eg [Finite G] (s : Swap z t w) (ha : Good z t a) {u : G} (hu : u ∈ Uz z)
    (hut : u * t * u⁻¹ = z * t) {x : G} (hx : x ∈ Eg z t w a) : u * x * u⁻¹ ∈ Eg z t w a := by
  have hp := s.cm
  obtain ⟨huz, -, -, -⟩ := s.u_facts hu hut
  refine conj_mem_closure (fun y hy => ?_) hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with h | h | h | h <;> rw [h]
  · rw [huz]; exact z_mem_Eg
  · rw [hut]; exact V_le_Eg (zt_mem_Vg z t)
  · have e : u * a * u⁻¹ = (u * a * u⁻¹ * a⁻¹) * a := by group
    have := s.hyp.comm_eq ⟨u, hu⟩ ⟨a, ha.mem.1⟩
    rw [e]
    refine mul_mem (V_le_Eg ?_) a_mem_Eg
    have e2 : u * a * u⁻¹ * a⁻¹ = _ := this
    rw [e2]
    exact zp_z_mem z t _
  · obtain ⟨hn'N, hX⟩ := s.key_B hu hut ha.mem
    have e : u * (w⁻¹ * a * w) * u⁻¹ = (w⁻¹ * a * w) *
        ((a * ((w⁻¹ * a * w)⁻¹ * (u * (w⁻¹ * a * w) * u⁻¹))⁻¹)⁻¹ * a) := by group
    rw [e]
    exact mul_mem m_mem_Eg (mul_mem (V_le_Eg ((Vg z t).inv_mem hX)) a_mem_Eg)

theorem w_conj_Eg [Finite G] (s : Swap z t w) (ha : Good z t a) {x : G} (hx : x ∈ Eg z t w a) :
    w * x * w⁻¹ ∈ Eg z t w a := by
  refine conj_mem_closure (fun y hy => ?_) hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with h | h | h | h <;> rw [h]
  · rw [s.w1']; exact t_mem_Eg
  · rw [s.w2']; exact z_mem_Eg
  · have e : w * a * w⁻¹ = (w * w) * (w⁻¹ * a * w) * (w * w)⁻¹ := by group
    rw [e]
    exact s.B_conj_Eg ha s.w_sq_mem_B m_mem_Eg
  · have e : w * (w⁻¹ * a * w) * w⁻¹ = a := by group
    rw [e]; exact a_mem_Eg

theorem T_le_normalizer [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Tn z t ≤ Subgroup.normalizer (Eg z t w a : Set G) := by
  obtain ⟨u, hu, hu'⟩ := s.exists_u0
  have hut : u * t * u⁻¹ = z * t := by
    calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
      _ = z * t := by rw [hu']
  have hnormB : ∀ b ∈ Bg z t, b ∈ Subgroup.normalizer (Eg z t w a : Set G) := fun b hb =>
    mem_normalizer_of_forward fun x hx => s.B_conj_Eg ha hb hx
  have hnormU : u ∈ Subgroup.normalizer (Eg z t w a : Set G) :=
    mem_normalizer_of_forward fun x hx => s.u_conj_Eg ha hu hut hx
  intro g hg
  rcases s.hyp.conj_t_cases s.ht hg with h1 | h1
  · exact hnormB g ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h1])⟩
  · obtain ⟨huz, huz', hut', huzt⟩ := s.u_facts hu hut
    have hbB : u⁻¹ * g ∈ Bg z t := by
      refine ⟨mul_mem ((Hz z).inv_mem (Uz_le_Hz z hu)) hg.1,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u⁻¹ * g * t = u⁻¹ * (g * t * g⁻¹) * g := by group
        _ = u⁻¹ * (z * t) * g := by rw [h1]
        _ = (u⁻¹ * z * u) * (u⁻¹ * t * u) * u⁻¹ * g := by group
        _ = z * (z * t) * u⁻¹ * g := by rw [huz', hut']
        _ = (z * z) * t * u⁻¹ * g := by group
        _ = t * (u⁻¹ * g) := by rw [s.hyp.sq_z, one_mul]; group
    have e : g = u * (u⁻¹ * g) := by group
    rw [e]
    exact mul_mem hnormU (hnormB _ hbB)

theorem normalizer_V_le [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Subgroup.normalizer (Vg z t : Set G) ≤ Subgroup.normalizer (Eg z t w a : Set G) := by
  have hp := s.cm
  obtain ⟨u, hu, hu'⟩ := s.exists_u0
  have hut : u * t * u⁻¹ = z * t := by
    calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
      _ = z * t := by rw [hu']
  obtain ⟨huz, huz', hut', huzt⟩ := s.u_facts hu hut
  have huT : u ∈ Tn z t :=
    s.hyp.mem_Tn_of s.ht (Uz_le_Hz z hu) (by rw [hut]; exact zt_mem_Vg z t)
  have hwN : w ∈ Subgroup.normalizer (Eg z t w a : Set G) :=
    mem_normalizer_of_forward fun x hx => s.w_conj_Eg ha hx
  have huN : u ∈ Subgroup.normalizer (Eg z t w a : Set G) := s.T_le_normalizer ha huT
  have hwV : w⁻¹ ∈ Subgroup.normalizer (Vg z t : Set G) :=
    hp.mem_normalizer_Vg (by simpa [s.w1] using t_mem_Vg z t)
      (by simpa [s.w2] using z_mem_Vg z t)
  have huV : u ∈ Subgroup.normalizer (Vg z t : Set G) := huT.2
  intro g hg
  have hgz : g * z * g⁻¹ ∈ Vg z t := (Subgroup.mem_normalizer_iff.mp hg z).mp (z_mem_Vg z t)
  have hg1 : g * z * g⁻¹ ≠ 1 := fun e => s.hyp.z_ne_one (by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  rcases (hp.mem_Vg_iff₄ _).1 hgz with e | e | e | e
  · exact absurd e hg1
  · exact s.T_le_normalizer ha ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [e]), hg⟩
  ·
    have hwg : w * g ∈ Tn z t := by
      have hzc : (w * g) * z * (w * g)⁻¹ = z := by
        calc (w * g) * z * (w * g)⁻¹ = w * (g * z * g⁻¹) * w⁻¹ := by group
          _ = z := by rw [e, s.w2']
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, mul_mem ?_ hg⟩
      · calc w * g * z = ((w * g) * z * (w * g)⁻¹) * (w * g) := by group
          _ = z * (w * g) := by rw [hzc]
      · have hwV' : w ∈ Subgroup.normalizer (Vg z t : Set G) := by
          have := (Subgroup.normalizer (Vg z t : Set G)).inv_mem hwV
          simpa using this
        exact hwV'
    have e2 : g = w⁻¹ * (w * g) := by group
    rw [e2]
    exact mul_mem ((Subgroup.normalizer (Eg z t w a : Set G)).inv_mem hwN)
      (s.T_le_normalizer ha hwg)
  ·
    have hyV : u * w⁻¹ ∈ Subgroup.normalizer (Vg z t : Set G) := mul_mem huV hwV
    have hyN : u * w⁻¹ ∈ Subgroup.normalizer (Eg z t w a : Set G) :=
      mul_mem huN ((Subgroup.normalizer (Eg z t w a : Set G)).inv_mem hwN)
    have hyg : (u * w⁻¹)⁻¹ * g ∈ Tn z t := by
      have hzc : ((u * w⁻¹)⁻¹ * g) * z * ((u * w⁻¹)⁻¹ * g)⁻¹ = z := by
        calc ((u * w⁻¹)⁻¹ * g) * z * ((u * w⁻¹)⁻¹ * g)⁻¹
            = w * u⁻¹ * (g * z * g⁻¹) * u * w⁻¹ := by group
          _ = w * (u⁻¹ * (z * t) * u) * w⁻¹ := by rw [e]; group
          _ = w * t * w⁻¹ := by rw [huzt]
          _ = z := s.w2'
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        mul_mem ((Subgroup.normalizer (Vg z t : Set G)).inv_mem hyV) hg⟩
      calc (u * w⁻¹)⁻¹ * g * z
          = (((u * w⁻¹)⁻¹ * g) * z * ((u * w⁻¹)⁻¹ * g)⁻¹) * ((u * w⁻¹)⁻¹ * g) := by group
        _ = z * ((u * w⁻¹)⁻¹ * g) := by rw [hzc]
    have e2 : g = (u * w⁻¹) * ((u * w⁻¹)⁻¹ * g) := by group
    rw [e2]
    exact mul_mem hyN (s.T_le_normalizer ha hyg)

end Swap

end CFSG.Quasithin.H13.U43
