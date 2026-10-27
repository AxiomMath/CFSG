module

public import CFSG.Quasithin.H13.GoldschmidtU43BCommute

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

abbrev Eg (z t w a : G) : Subgroup G := Subgroup.closure {z, t, a, w⁻¹ * a * w}

structure Good (z t a : G) : Prop where
  mem : a ∈ N1g z t
  sq : a * a = 1
  notV : a ∉ Vg z t

namespace Swap

variable {z t w a : G}

theorem B_le_T [Finite G] (s : Swap z t w) : Bg z t ≤ Tn z t := fun b hb =>
  s.hyp.mem_Tn_of s.ht hb.1 (by
    have : b * t * b⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hb.2
      calc b * t * b⁻¹ = (t * b) * b⁻¹ := by rw [this]
        _ = t := by group
    rw [this]
    exact t_mem_Vg z t)

theorem w_conj_mem_V (s : Swap z t w) {v : G} (hv : v ∈ Vg z t) : w * v * w⁻¹ ∈ Vg z t :=
  s.cm.conj_mem_of_mem (by rw [s.w1']; exact t_mem_Vg z t)
    (by rw [s.w2']; exact z_mem_Vg z t) hv

theorem m_mem_N2 (ha : Good z t a) : w⁻¹ * a * w ∈ N2g z t w := by
  rw [mem_N2]
  have e : w * (w⁻¹ * a * w) * w⁻¹ = a := by group
  rw [e]
  exact ha.mem

theorem m_mem_B (s : Swap z t w) (ha : Good z t a) : w⁻¹ * a * w ∈ Bg z t :=
  s.N2_le_B (m_mem_N2 ha)

theorem m_sq (ha : Good z t a) : (w⁻¹ * a * w) * (w⁻¹ * a * w) = 1 := by
  calc (w⁻¹ * a * w) * (w⁻¹ * a * w) = w⁻¹ * (a * a) * w := by group
    _ = 1 := by rw [ha.sq]; group

theorem m_notV (s : Swap z t w) (ha : Good z t a) : w⁻¹ * a * w ∉ Vg z t := by
  intro hm
  apply ha.notV
  have := s.w_conj_mem_V hm
  have e : w * (w⁻¹ * a * w) * w⁻¹ = a := by group
  rwa [e] at this

theorem am_notV (s : Swap z t w) (ha : Good z t a) : a * (w⁻¹ * a * w) ∉ Vg z t := by
  intro h
  apply s.m_notV ha
  refine (s.mem_N1_inf_N2 _).1 ⟨?_, m_mem_N2 ha⟩
  have e : w⁻¹ * a * w = a⁻¹ * (a * (w⁻¹ * a * w)) := by group
  rw [e]
  exact mul_mem ((N1g z t).inv_mem ha.mem) (s.Vg_le_N1 h)

theorem a_comm_m [Finite G] (s : Swap z t w) (ha : Good z t a) :
    a * (w⁻¹ * a * w) = (w⁻¹ * a * w) * a :=
  s.commute_conj ha.mem

theorem zp_mem_B (ha : Good z t a) (i : ZMod 2) : zp a i ∈ Bg z t := by
  rcases zmod_two_cases i with rfl | rfl
  · rw [zp_zero]; exact one_mem _
  · rw [zp_one]; exact N1_le_B ha.mem

theorem zp_m_mem_B (s : Swap z t w) (ha : Good z t a) (j : ZMod 2) :
    zp (w⁻¹ * a * w) j ∈ Bg z t := by
  rcases zmod_two_cases j with rfl | rfl
  · rw [zp_zero]; exact one_mem _
  · rw [zp_one]; exact s.m_mem_B ha

theorem zp_comm_am [Finite G] (s : Swap z t w) (ha : Good z t a) (i j : ZMod 2) :
    zp a i * zp (w⁻¹ * a * w) j = zp (w⁻¹ * a * w) j * zp a i := by
  rcases zmod_two_cases i with rfl | rfl <;> rcases zmod_two_cases j with rfl | rfl <;>
    simp [zp_zero, zp_one, s.a_comm_m ha]

theorem Eg_mul_formula [Finite G] (s : Swap z t w) (ha : Good z t a) {v v' : G}
    (hv' : v' ∈ Vg z t) (i j i' j' : ZMod 2) :
    (v * zp a i * zp (w⁻¹ * a * w) j) * (v' * zp a i' * zp (w⁻¹ * a * w) j') =
      (v * v') * zp a (i + i') * zp (w⁻¹ * a * w) (j + j') := by
  have hMv : zp (w⁻¹ * a * w) j * v' = v' * zp (w⁻¹ * a * w) j :=
    s.V_central (s.zp_m_mem_B ha j) hv'
  have hAv : zp a i * v' = v' * zp a i := s.V_central (zp_mem_B ha i) hv'
  have hMA : zp (w⁻¹ * a * w) j * zp a i' = zp a i' * zp (w⁻¹ * a * w) j :=
    (s.zp_comm_am ha i' j).symm
  have hm2 : (w⁻¹ * a * w) * (w⁻¹ * a * w) = 1 := m_sq ha
  calc (v * zp a i * zp (w⁻¹ * a * w) j) * (v' * zp a i' * zp (w⁻¹ * a * w) j')
      = v * zp a i * (zp (w⁻¹ * a * w) j * v') * zp a i' * zp (w⁻¹ * a * w) j' := by group
    _ = v * zp a i * (v' * zp (w⁻¹ * a * w) j) * zp a i' * zp (w⁻¹ * a * w) j' := by rw [hMv]
    _ = v * (zp a i * v') * zp (w⁻¹ * a * w) j * zp a i' * zp (w⁻¹ * a * w) j' := by group
    _ = v * (v' * zp a i) * zp (w⁻¹ * a * w) j * zp a i' * zp (w⁻¹ * a * w) j' := by rw [hAv]
    _ = (v * v') * zp a i * (zp (w⁻¹ * a * w) j * zp a i') * zp (w⁻¹ * a * w) j' := by group
    _ = (v * v') * zp a i * (zp a i' * zp (w⁻¹ * a * w) j) * zp (w⁻¹ * a * w) j' := by rw [hMA]
    _ = (v * v') * (zp a i * zp a i') * (zp (w⁻¹ * a * w) j * zp (w⁻¹ * a * w) j') := by group
    _ = (v * v') * zp a (i + i') * zp (w⁻¹ * a * w) (j + j') := by
        rw [zp_add ha.sq, zp_add hm2]

theorem V_le_Eg : Vg z t ≤ Eg z t w a :=
  Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

theorem V_sq (s : Swap z t w) {v : G} (hv : v ∈ Vg z t) : v * v = 1 := by
  have hp := s.cm
  rcases (hp.mem_Vg_iff₄ _).1 hv with rfl | rfl | rfl | rfl
  · simp
  · exact hp.sq_z
  · exact hp.sq_t
  · calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hp.comm]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hp.sq_z, hp.sq_t, mul_one]

theorem mem_Eg_iff [Finite G] (s : Swap z t w) (ha : Good z t a) (x : G) :
    x ∈ Eg z t w a ↔ ∃ v ∈ Vg z t, ∃ i j : ZMod 2, x = v * zp a i * zp (w⁻¹ * a * w) j := by
  have hm2 : (w⁻¹ * a * w) * (w⁻¹ * a * w) = 1 := m_sq ha
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨y, z_mem_Vg y t, 0, 0, by simp [zp_zero]⟩
      · exact ⟨y, t_mem_Vg z y, 0, 0, by simp [zp_zero]⟩
      · exact ⟨1, one_mem _, 1, 0, by simp [zp_zero, zp_one]⟩
      · exact ⟨1, one_mem _, 0, 1, by simp [zp_zero, zp_one]⟩
    | one => exact ⟨1, one_mem _, 0, 0, by simp [zp_zero]⟩
    | mul y y' _ _ ih ih' =>
      obtain ⟨v, hv, i, j, rfl⟩ := ih
      obtain ⟨v', hv', i', j', rfl⟩ := ih'
      exact ⟨v * v', mul_mem hv hv', i + i', j + j', s.Eg_mul_formula ha hv' i j i' j'⟩
    | inv y _ ih =>
      obtain ⟨v, hv, i, j, rfl⟩ := ih
      refine ⟨v⁻¹, (Vg z t).inv_mem hv, i, j, ?_⟩
      have hMv : zp (w⁻¹ * a * w) j * v⁻¹ = v⁻¹ * zp (w⁻¹ * a * w) j :=
        s.V_central (s.zp_m_mem_B ha j) ((Vg z t).inv_mem hv)
      have hAv : zp a i * v⁻¹ = v⁻¹ * zp a i :=
        s.V_central (zp_mem_B ha i) ((Vg z t).inv_mem hv)
      have hMA := s.zp_comm_am ha i j
      calc (v * zp a i * zp (w⁻¹ * a * w) j)⁻¹
          = (zp (w⁻¹ * a * w) j)⁻¹ * (zp a i)⁻¹ * v⁻¹ := by group
        _ = zp (w⁻¹ * a * w) j * zp a i * v⁻¹ := by rw [zp_inv hm2, zp_inv ha.sq]
        _ = zp a i * zp (w⁻¹ * a * w) j * v⁻¹ := by rw [← hMA]
        _ = zp a i * (zp (w⁻¹ * a * w) j * v⁻¹) := by group
        _ = zp a i * (v⁻¹ * zp (w⁻¹ * a * w) j) := by rw [hMv]
        _ = (zp a i * v⁻¹) * zp (w⁻¹ * a * w) j := by group
        _ = (v⁻¹ * zp a i) * zp (w⁻¹ * a * w) j := by rw [hAv]
  · rintro ⟨v, hv, i, j, rfl⟩
    refine mul_mem (mul_mem (V_le_Eg hv) ?_) ?_
    · rcases zmod_two_cases i with rfl | rfl
      · rw [zp_zero]; exact one_mem _
      · rw [zp_one]; exact Subgroup.subset_closure (by simp)
    · rcases zmod_two_cases j with rfl | rfl
      · rw [zp_zero]; exact one_mem _
      · rw [zp_one]; exact Subgroup.subset_closure (by simp)

theorem Eg_le_B (s : Swap z t w) (ha : Good z t a) : Eg z t w a ≤ Bg z t := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact N1_le_B (s.Vg_le_N1 (z_mem_Vg x t))
  · exact N1_le_B (s.Vg_le_N1 (t_mem_Vg z x))
  · exact N1_le_B ha.mem
  · exact s.m_mem_B ha

theorem Eg_comm_sq [Finite G] (s : Swap z t w) (ha : Good z t a) {x y : G}
    (hx : x ∈ Eg z t w a) (hy : y ∈ Eg z t w a) : x * y = y * x ∧ x * x = 1 := by
  obtain ⟨v, hv, i, j, rfl⟩ := (s.mem_Eg_iff ha x).1 hx
  obtain ⟨v', hv', i', j', rfl⟩ := (s.mem_Eg_iff ha y).1 hy
  have hvv : v * v' = v' * v := s.V_central (N1_le_B (s.Vg_le_N1 hv)) hv'
  refine ⟨?_, ?_⟩
  · rw [s.Eg_mul_formula ha hv' i j i' j', s.Eg_mul_formula ha hv i' j' i j, hvv, add_comm i,
      add_comm j]
  · have e := s.Eg_mul_formula ha (v := v) (v' := v) hv i j i j
    have h2 : ∀ k : ZMod 2, k + k = 0 := by decide
    rw [e, s.V_sq hv, h2 i, h2 j, zp_zero, zp_zero]
    simp

theorem Eg_inj [Finite G] (s : Swap z t w) (ha : Good z t a) {v v' : G} (hv : v ∈ Vg z t)
    (hv' : v' ∈ Vg z t) {i j i' j' : ZMod 2}
    (h : v * zp a i * zp (w⁻¹ * a * w) j = v' * zp a i' * zp (w⁻¹ * a * w) j') :
    v = v' ∧ i = i' ∧ j = j' := by
  have hY : v' * zp a i' * zp (w⁻¹ * a * w) j' ∈ Eg z t w a :=
    (s.mem_Eg_iff ha _).2 ⟨v', hv', i', j', rfl⟩
  have hYY := (s.Eg_comm_sq ha hY hY).2
  have hprod : (v * v') * zp a (i + i') * zp (w⁻¹ * a * w) (j + j') = 1 := by
    rw [← s.Eg_mul_formula ha hv' i j i' j', h, hYY]
  have hAM : zp a (i + i') * zp (w⁻¹ * a * w) (j + j') ∈ Vg z t := by
    have : zp a (i + i') * zp (w⁻¹ * a * w) (j + j') = (v * v')⁻¹ :=
      eq_inv_of_mul_eq_one_right (by simpa [mul_assoc] using hprod)
    rw [this]
    exact (Vg z t).inv_mem (mul_mem hv hv')
  have hi : ∀ k l : ZMod 2, k + l = 0 → k = l := by decide
  rcases zmod_two_cases (i + i') with e1 | e1 <;> rcases zmod_two_cases (j + j') with e2 | e2
  · have hii := hi _ _ e1
    have hjj := hi _ _ e2
    subst hii
    subst hjj
    have : v = v' := by simpa using h
    exact ⟨this, rfl, rfl⟩
  · exfalso
    rw [e1, e2, zp_zero, zp_one, one_mul] at hAM
    exact s.m_notV ha hAM
  · exfalso
    rw [e1, e2, zp_zero, zp_one, mul_one] at hAM
    exact ha.notV hAM
  · exfalso
    rw [e1, e2, zp_one, zp_one] at hAM
    exact s.am_notV ha hAM

theorem card_Eg [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Nat.card ↥(Eg z t w a) = 16 := by
  classical
  let f : ↥(Vg z t) × ZMod 2 × ZMod 2 → G := fun p =>
    (p.1 : G) * zp a p.2.1 * zp (w⁻¹ * a * w) p.2.2
  have hrange : (Eg z t w a : Set G) = Set.range f := by
    ext x
    rw [SetLike.mem_coe, s.mem_Eg_iff ha]
    constructor
    · rintro ⟨v, hv, i, j, rfl⟩
      exact ⟨(⟨v, hv⟩, i, j), rfl⟩
    · rintro ⟨⟨⟨v, hv⟩, i, j⟩, rfl⟩
      exact ⟨v, hv, i, j, rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨v, hv⟩, i, j⟩ ⟨⟨v', hv'⟩, i', j'⟩ h
    obtain ⟨h1, h2, h3⟩ := s.Eg_inj ha hv hv' (show v * zp a i * zp (w⁻¹ * a * w) j =
      v' * zp a i' * zp (w⁻¹ * a * w) j' from h)
    subst h1 h2 h3
    rfl
  rw [show Nat.card ↥(Eg z t w a) = Nat.card (Set.range f) from
    congrArg Nat.card (congrArg (fun S : Set G => ↥S) hrange), Nat.card_range_of_injective hinj]
  simp [Nat.card_prod, s.card_Vg]

end Swap

end CFSG.Quasithin.H13.U43
