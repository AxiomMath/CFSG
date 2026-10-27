module

public import CFSG.Quasithin.H13.GoldschmidtU43DForm

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def Fvb (u v : V4) : ZMod 2 := u 0 * v 3 + u 1 * v 2 + u 2 * v 1 + u 3 * v 0

theorem add_lin {g : V4 → ZMod 2} (hg : ∀ u u', g (u + u') = g u + g u') (u : V4) :
    g u = u 0 * g (idc 0) + u 1 * g (idc 1) + u 2 * g (idc 2) + u 3 * g (idc 3) := by
  have g0 : g 0 = 0 := by
    have := hg 0 0
    rw [add_zero] at this
    simpa using this
  have gs : ∀ (x : ZMod 2) (e : V4), g (x • e) = x * g e := by
    intro x e
    rcases zmod_two_cases x with rfl | rfl
    · simp [g0]
    · simp
  conv_lhs => rw [eq_sum_idc u]
  rw [hg, hg, hg, gs, gs, gs, gs]

theorem biadd_ext {f f' : V4 → V4 → ZMod 2} (h1 : ∀ u u' v, f (u + u') v = f u v + f u' v)
    (h2 : ∀ u v v', f u (v + v') = f u v + f u v')
    (h1' : ∀ u u' v, f' (u + u') v = f' u v + f' u' v)
    (h2' : ∀ u v v', f' u (v + v') = f' u v + f' u v')
    (hb : ∀ i j, f (idc i) (idc j) = f' (idc i) (idc j)) (u v : V4) : f u v = f' u v := by
  have e1 : f u v = u 0 * f (idc 0) v + u 1 * f (idc 1) v + u 2 * f (idc 2) v +
      u 3 * f (idc 3) v := add_lin (g := fun u => f u v) (fun u u' => h1 u u' v) u
  have e1' : f' u v = u 0 * f' (idc 0) v + u 1 * f' (idc 1) v + u 2 * f' (idc 2) v +
      u 3 * f' (idc 3) v := add_lin (g := fun u => f' u v) (fun u u' => h1' u u' v) u
  have e2 : ∀ i, f (idc i) v = v 0 * f (idc i) (idc 0) + v 1 * f (idc i) (idc 1) +
      v 2 * f (idc i) (idc 2) + v 3 * f (idc i) (idc 3) := fun i =>
    add_lin (g := fun v => f (idc i) v) (fun v v' => h2 (idc i) v v') v
  have e2' : ∀ i, f' (idc i) v = v 0 * f' (idc i) (idc 0) + v 1 * f' (idc i) (idc 1) +
      v 2 * f' (idc i) (idc 2) + v 3 * f' (idc i) (idc 3) := fun i =>
    add_lin (g := fun v => f' (idc i) v) (fun v v' => h2' (idc i) v v') v
  rw [e1, e1', e2 0, e2 1, e2 2, e2 3, e2' 0, e2' 1, e2' 2, e2' 3]
  simp only [hb]

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

theorem Fv_add_left (c c' d : V4) :
    Fv z t w a (c + c') d = Fv z t w a c d + Fv z t w a c' d := by
  calc Fv z t w a (c + c') d = Fv z t w a d (c + c') := s.Fv_symm ha _ _
    _ = Fv z t w a d c + Fv z t w a d c' := s.Fv_add_right ha _ _ _
    _ = Fv z t w a c d + Fv z t w a c' d := by rw [s.Fv_symm ha d c, s.Fv_symm ha d c']

theorem Fv_zero_right (c : V4) : Fv z t w a c 0 = 0 := by
  have := s.Fv_add_right ha c 0 0
  rw [add_zero] at this
  simpa using this

theorem Fv_smul_right (c d : V4) (x : ZMod 2) :
    Fv z t w a c (x • d) = x * Fv z t w a c d := by
  rcases zmod_two_cases x with rfl | rfl
  · simp [s.Fv_zero_right ha]
  · simp

theorem Fv_smul_left (c d : V4) (x : ZMod 2) :
    Fv z t w a (x • c) d = x * Fv z t w a c d := by
  rw [s.Fv_symm ha, s.Fv_smul_right ha, s.Fv_symm ha]

omit [Finite G] s ha in
theorem Fv_idc (i j : Fin 4) : Fv z t w a (idc i) (idc j) =
    open Classical in if gE z t w a j ∈ Uz (gE z t w a i) then 0 else 1 := by
  have hi : (idc i : V4) ≠ 0 := by
    fin_cases i <;> decide
  unfold Fv
  simp only [hi, ↓reduceIte]
  rw [crd_idc, crd_idc]

omit [Finite G] in
theorem m_mem_Uz_t : w⁻¹ * a * w ∈ Uz t := by
  have e : t = w⁻¹ * z * w⁻¹⁻¹ := by
    rw [inv_inv]
    exact s.w1.symm
  rw [e, mem_Uz_conj]
  have e2 : (w⁻¹)⁻¹ * (w⁻¹ * a * w) * w⁻¹ = a := by group
  rw [e2]
  exact ha.mem.1

omit [Finite G] ha in
theorem Fv_01 : Fv z t w a (idc 0) (idc 1) = 0 := by
  rw [Fv_idc]
  have h1 : t ∈ Uz z := s.ht.1
  simp [gE, h1]

omit [Finite G] s in
theorem Fv_02 : Fv z t w a (idc 0) (idc 2) = 0 := by
  rw [Fv_idc]
  have h1 : a ∈ Uz z := ha.mem.1
  simp [gE, h1]

omit [Finite G] in
theorem Fv_03 : Fv z t w a (idc 0) (idc 3) = 1 := by
  rw [Fv_idc]
  simp [gE, s.m_not_mem_U ha]

omit [Finite G] in
theorem Fv_13 : Fv z t w a (idc 1) (idc 3) = 0 := by
  rw [Fv_idc]
  have := s.m_mem_Uz_t ha
  simp [gE, this]

theorem Fv_12 : Fv z t w a (idc 1) (idc 2) = 1 := by
  have hc : (idc 1 : V4) ≠ 0 := by decide
  obtain ⟨d, hd⟩ := s.Fv_nondeg ha hc
  have hlin := add_lin (g := fun d => Fv z t w a (idc 1) d) (fun d d' => s.Fv_add_right ha _ _ _) d
  have h10 : Fv z t w a (idc 1) (idc 0) = 0 := by rw [s.Fv_symm ha]; exact s.Fv_01
  have h11 : Fv z t w a (idc 1) (idc 1) = 0 := s.Fv_self ha _
  have h13 := s.Fv_13 ha
  rw [h10, h11, h13] at hlin
  rw [hlin] at hd
  have hd2 : d 2 * Fv z t w a (idc 1) (idc 2) = 1 := by simpa using hd
  rcases zmod_two_cases (Fv z t w a (idc 1) (idc 2)) with h0 | h1
  · rw [h0] at hd2
    simp at hd2
  · exact h1

end Swap

@[expose] def Cmat (l : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, l, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem Cmat_mul_self : ∀ l : ZMod 2, Cmat l * Cmat l = 1 := by
  decide +kernel

theorem Cmat_mulVec_idc : ∀ l : ZMod 2, (Cmat l).mulVec (idc 0) = idc 0 ∧
    (Cmat l).mulVec (idc 1) = idc 1 ∧ (Cmat l).mulVec (idc 2) = idc 2 + l • idc 0 ∧
    (Cmat l).mulVec (idc 3) = idc 3 := by
  decide +kernel

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

theorem Fv_Cmat (u v : V4) : Fv z t w a ((Cmat (Fv z t w a (idc 2) (idc 3))).mulVec u)
    ((Cmat (Fv z t w a (idc 2) (idc 3))).mulVec v) = Fvb u v := by
  set l := Fv z t w a (idc 2) (idc 3) with hl
  obtain ⟨hP0, hP1, hP2, hP3⟩ := Cmat_mulVec_idc l
  have hll : l + l = 0 := by
    rcases zmod_two_cases l with h | h <;> rw [h] <;> decide
  have h00 := s.Fv_self ha (idc 0)
  have h11 := s.Fv_self ha (idc 1)
  have h22 := s.Fv_self ha (idc 2)
  have h33 := s.Fv_self ha (idc 3)
  have h01 := s.Fv_01 (a := a)
  have h02 := Fv_02 (w := w) ha
  have h03 := s.Fv_03 ha
  have h12 := s.Fv_12 ha
  have h13 := s.Fv_13 ha
  have h10 : Fv z t w a (idc 1) (idc 0) = 0 := by rw [s.Fv_symm ha]; exact h01
  have h20 : Fv z t w a (idc 2) (idc 0) = 0 := by rw [s.Fv_symm ha]; exact h02
  have h30 : Fv z t w a (idc 3) (idc 0) = 1 := by rw [s.Fv_symm ha]; exact h03
  have h21 : Fv z t w a (idc 2) (idc 1) = 1 := by rw [s.Fv_symm ha]; exact h12
  have h31 : Fv z t w a (idc 3) (idc 1) = 0 := by rw [s.Fv_symm ha]; exact h13
  have h32 : Fv z t w a (idc 3) (idc 2) = l := by rw [s.Fv_symm ha]
  refine biadd_ext (f := fun u v => Fv z t w a ((Cmat l).mulVec u) ((Cmat l).mulVec v))
    (f' := Fvb) ?_ ?_ ?_ ?_ ?_ u v
  · intro u u' v
    simp only [Matrix.mulVec_add, s.Fv_add_left ha]
  · intro u v v'
    simp only [Matrix.mulVec_add, s.Fv_add_right ha]
  · intro u u' v
    unfold Fvb
    simp only [Pi.add_apply]
    ring
  · intro u v v'
    unfold Fvb
    simp only [Pi.add_apply]
    ring
  · intro i j
    have hb : Fvb (idc i) (idc j) = if (i : ℕ) + j = 3 then 1 else 0 := by
      fin_cases i <;> fin_cases j <;> decide
    rw [hb]
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, hP0, hP1, hP2, hP3, s.Fv_add_left ha, s.Fv_add_right ha, s.Fv_smul_left ha,
      s.Fv_smul_right ha, h00, h11, h22, h33, h01, h02, h03, h12, h13, h10, h20, h30, h21, h31,
      h32]
    all_goals simp [← hl, hll]

end Swap

end CFSG.Quasithin.H13.U43
