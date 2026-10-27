module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelW1

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def E1 : VM := mkV (ex 1) 0
@[expose] def E2 : VM := mkV (ex 2) 0
@[expose] def F1 : VM := mkV 0 (ex 1)
@[expose] def F2 : VM := mkV 0 (ex 2)

@[expose] def cvec (a1 a2 a3 a4 : ZMod 2) : VM :=
  mkV ![0, a4, a3] ![0, a1, a2]

@[expose] def projU (v : VM) : VM := v - v (Sum.inl 0) • e0 - v (Sum.inr 0) • f0

theorem bM_add_left (v w x : VM) : bM (v + w) x = bM v x + bM w x := by
  simp only [bM, xp_add, yp_add, dotProduct, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem bM_smul_left (a : ZMod 2) (v x : VM) : bM (a • v) x = a * bM v x := by
  simp only [bM, xp_smul, yp_smul, dotProduct, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem bM_sub_left (v w x : VM) : bM (v - w) x = bM v x - bM w x := by
  simp only [bM, xp, yp, dotProduct, Pi.sub_apply, Fin.sum_univ_three]
  ring

theorem bM_of_GM {γ : VM ≃ₗ[ZMod 2] VM} (hγ : γ ∈ GM) (x y : VM) :
    bM (γ x) (γ y) = bM x y := by
  have h1 := qM_add x y
  have h2 := qM_add (γ x) (γ y)
  have e1 : qM (γ x + γ y) = qM (x + y) := by
    rw [← map_add]
    exact hγ (x + y)
  have hx : qM (γ x) = qM x := hγ x
  have hy : qM (γ y) = qM y := hγ y
  rw [e1, hx, hy] at h2
  linear_combination h1 - h2

theorem bM_e0_f0 : bM f0 e0 = 1 := by
  rw [bM_e0_right]
  simp [f0, mkV, ex, Pi.single_apply]

theorem bM_f0_u (u : VM) (hu : u (Sum.inl 0) = 0) : bM f0 u = 0 := by
  rw [bM_symm]
  simp [bM, f0, xp, yp, mkV, ex, dotProduct, Fin.sum_univ_three, hu]

theorem bM_E1 (a1 a2 a3 a4 : ZMod 2) : bM E1 (cvec a1 a2 a3 a4) = a1 := by
  simp [bM, E1, cvec, xp, yp, mkV, ex, dotProduct, Fin.sum_univ_three]

theorem bM_E2 (a1 a2 a3 a4 : ZMod 2) : bM E2 (cvec a1 a2 a3 a4) = a2 := by
  simp [bM, E2, cvec, xp, yp, mkV, ex, dotProduct, Fin.sum_univ_three]

theorem bM_F1 (a1 a2 a3 a4 : ZMod 2) : bM F1 (cvec a1 a2 a3 a4) = a4 := by
  simp [bM, F1, cvec, xp, yp, mkV, ex, dotProduct, Fin.sum_univ_three]

theorem bM_F2 (a1 a2 a3 a4 : ZMod 2) : bM F2 (cvec a1 a2 a3 a4) = a3 := by
  simp [bM, F2, cvec, xp, yp, mkV, ex, dotProduct, Fin.sum_univ_three]

theorem inU_cvec (a1 a2 a3 a4 : ZMod 2) : inU (cvec a1 a2 a3 a4) := by
  simp [inU, cvec, mkV]

theorem inU_projU (v : VM) : inU (projU v) := by
  refine ⟨?_, ?_⟩ <;> simp [projU, e0, f0, mkV, ex, Pi.single_apply] <;> ring

theorem projU_decomp (v : VM) : v = v (Sum.inl 0) • e0 + v (Sum.inr 0) • f0 + projU v := by
  unfold projU
  abel

theorem EL_apply_of_inr (c : VM) (hc : inU c) (v : VM) (hv : v (Sum.inr 0) = 0) :
    EL c hc v = v + bM v c • e0 := by
  simp [EL_apply, Eev, hv]

theorem EL_f0 (c : VM) (hc : inU c) : EL c hc f0 = qM c • e0 + f0 + c := by
  rw [EL_apply, Eev]
  have h1 : f0 (Sum.inr 0) = 1 := by simp [f0, mkV, ex, Pi.single_apply]
  have h2 : bM f0 c = 0 := bM_f0_u c hc.1
  rw [h1, h2, one_smul, zero_add, mul_one]
  abel

theorem qM_f0 : qM f0 = 0 := by
  simp [qM, f0, xp, yp, mkV, dotProduct, Fin.sum_univ_three]

theorem rad_e0 : ∀ v : VM, bM v e0 = 0 → bM v E1 = 0 → bM v E2 = 0 → bM v F1 = 0 →
    bM v F2 = 0 → v = 0 ∨ v = e0 := by
  decide +kernel

theorem decomp6 : ∀ x : VM, x = x (Sum.inl 0) • e0 + x (Sum.inr 0) • f0 + x (Sum.inl 1) • E1 +
    x (Sum.inl 2) • E2 + x (Sum.inr 1) • F1 + x (Sum.inr 2) • F2 := by
  decide +kernel

theorem kw_char (γ : VM ≃ₗ[ZMod 2] VM) (hγ : γ ∈ GM) (he0 : γ e0 = e0)
    (hcond : ∀ x, bM x e0 = 0 → γ x - x ∈ Submodule.span (ZMod 2) {e0}) :
    ∃ c : VM, ∃ hc : inU c, γ = EL c hc := by
  have coef : ∀ u : VM, bM u e0 = 0 → ∃ a : ZMod 2, γ u - u = a • e0 := by
    intro u hu
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hcond u hu)
    exact ⟨a, ha.symm⟩
  have hE1 : bM E1 e0 = 0 := by simp [bM_e0_right, E1, mkV, ex, Pi.single_apply]
  have hE2 : bM E2 e0 = 0 := by simp [bM_e0_right, E2, mkV, ex, Pi.single_apply]
  have hF1 : bM F1 e0 = 0 := by simp [bM_e0_right, F1, mkV, ex, Pi.single_apply]
  have hF2 : bM F2 e0 = 0 := by simp [bM_e0_right, F2, mkV, ex, Pi.single_apply]
  have hE1r : E1 (Sum.inr 0) = 0 := by simp [E1, mkV, ex, Pi.single_apply]
  have hE2r : E2 (Sum.inr 0) = 0 := by simp [E2, mkV, ex, Pi.single_apply]
  have hF1l : F1 (Sum.inl 0) = 0 := by simp [F1, mkV, ex, Pi.single_apply]
  have hF2l : F2 (Sum.inl 0) = 0 := by simp [F2, mkV, ex, Pi.single_apply]
  have hE1l : E1 (Sum.inl 0) = 0 := by simp [E1, mkV, ex, Pi.single_apply]
  have hE2l : E2 (Sum.inl 0) = 0 := by simp [E2, mkV, ex, Pi.single_apply]
  obtain ⟨a1, ha1⟩ := coef E1 hE1
  obtain ⟨a2, ha2⟩ := coef E2 hE2
  obtain ⟨a4, ha4⟩ := coef F1 hF1
  obtain ⟨a3, ha3⟩ := coef F2 hF2
  have hc : inU (cvec a1 a2 a3 a4) := inU_cvec a1 a2 a3 a4
  refine ⟨cvec a1 a2 a3 a4, hc, ?_⟩
  have hE1' : γ E1 = a1 • e0 + E1 := sub_eq_iff_eq_add.1 ha1
  have hE2' : γ E2 = a2 • e0 + E2 := sub_eq_iff_eq_add.1 ha2
  have hF1' : γ F1 = a4 • e0 + F1 := sub_eq_iff_eq_add.1 ha4
  have hF2' : γ F2 = a3 • e0 + F2 := sub_eq_iff_eq_add.1 ha3
  have hcE1 : bM (cvec a1 a2 a3 a4) E1 = a1 := by rw [bM_symm]; exact bM_E1 a1 a2 a3 a4
  have hcE2 : bM (cvec a1 a2 a3 a4) E2 = a2 := by rw [bM_symm]; exact bM_E2 a1 a2 a3 a4
  have hcF1 : bM (cvec a1 a2 a3 a4) F1 = a4 := by rw [bM_symm]; exact bM_F1 a1 a2 a3 a4
  have hcF2 : bM (cvec a1 a2 a3 a4) F2 = a3 := by rw [bM_symm]; exact bM_F2 a1 a2 a3 a4
  have hcE0 : bM (cvec a1 a2 a3 a4) e0 = 0 := by rw [bM_e0_right]; exact hc.2
  have hbfe : bM (γ f0) e0 = 1 := by
    have h := bM_of_GM hγ f0 e0
    rw [he0, bM_e0_f0] at h
    exact h
  have hf0E1 : bM f0 E1 = 0 := bM_f0_u E1 hE1l
  have hf0E2 : bM f0 E2 = 0 := bM_f0_u E2 hE2l
  have hf0F1 : bM f0 F1 = 0 := bM_f0_u F1 hF1l
  have hf0F2 : bM f0 F2 = 0 := bM_f0_u F2 hF2l
  have hval : ∀ u : VM, ∀ a : ZMod 2, γ u = a • e0 + u → bM f0 u = 0 → bM (γ f0) u = a := by
    intro u a hu hb
    have h := bM_of_GM hγ f0 u
    rw [hu, bM_symm (γ f0) (a • e0 + u), bM_add_left, bM_smul_left, bM_symm e0 (γ f0), hbfe,
      mul_one, hb] at h
    rw [bM_symm]
    exact (zmod2_sum_zero_eq _ _ h).symm
  have hbE1 : bM (γ f0) E1 = a1 := hval E1 a1 hE1' hf0E1
  have hbE2 : bM (γ f0) E2 = a2 := hval E2 a2 hE2' hf0E2
  have hbF1 : bM (γ f0) F1 = a4 := hval F1 a4 hF1' hf0F1
  have hbF2 : bM (γ f0) F2 = a3 := hval F2 a3 hF2' hf0F2
  have hrad := rad_e0 (γ f0 - f0 - cvec a1 a2 a3 a4)
    (by rw [bM_sub_left, bM_sub_left, hbfe, bM_e0_f0, hcE0]; ring)
    (by rw [bM_sub_left, bM_sub_left, hbE1, hf0E1, hcE1]; ring)
    (by rw [bM_sub_left, bM_sub_left, hbE2, hf0E2, hcE2]; ring)
    (by rw [bM_sub_left, bM_sub_left, hbF1, hf0F1, hcF1]; ring)
    (by rw [bM_sub_left, bM_sub_left, hbF2, hf0F2, hcF2]; ring)
  have hqf0 : qM (γ f0) = 0 := by rw [hγ f0, qM_f0]
  have hf0 : γ f0 = qM (cvec a1 a2 a3 a4) • e0 + f0 + cvec a1 a2 a3 a4 := by
    have e1 : γ f0 = (γ f0 - f0 - cvec a1 a2 a3 a4) + (f0 + cvec a1 a2 a3 a4) := by abel
    rcases hrad with hz | hz
    · rw [hz, zero_add] at e1
      have hq : qM (cvec a1 a2 a3 a4) = 0 := by
        have h := hqf0
        rw [e1, qM_add, bM_f0_u _ hc.1, qM_f0] at h
        linear_combination h
      rw [e1, hq, zero_smul, zero_add]
    · rw [hz] at e1
      have hbe : bM e0 (f0 + cvec a1 a2 a3 a4) = 1 := by
        rw [bM_symm, bM_add_left, bM_e0_f0, hcE0, add_zero]
      have hq : qM (cvec a1 a2 a3 a4) = 1 := by
        have h := hqf0
        rw [e1, qM_add, qM_add, qM_e0, qM_f0, bM_f0_u _ hc.1, hbe] at h
        have h' : qM (cvec a1 a2 a3 a4) + 1 = 0 := by linear_combination h
        exact zmod2_sum_zero_eq _ _ h'
      rw [e1, hq, one_smul]
      abel
  apply LinearEquiv.ext
  intro x
  rw [decomp6 x]
  have hγe0 : γ e0 = EL (cvec a1 a2 a3 a4) hc e0 := by rw [EL_e0, he0]
  have hγf0 : γ f0 = EL (cvec a1 a2 a3 a4) hc f0 := by rw [EL_f0, hf0]
  have hγE1 : γ E1 = EL (cvec a1 a2 a3 a4) hc E1 := by
    rw [EL_apply_of_inr _ hc E1 hE1r, bM_E1, hE1', add_comm]
  have hγE2 : γ E2 = EL (cvec a1 a2 a3 a4) hc E2 := by
    rw [EL_apply_of_inr _ hc E2 hE2r, bM_E2, hE2', add_comm]
  have hγF1 : γ F1 = EL (cvec a1 a2 a3 a4) hc F1 := by
    rw [EL_apply_of_inr _ hc F1 (by simp [F1, mkV, ex, Pi.single_apply]), bM_F1, hF1', add_comm]
  have hγF2 : γ F2 = EL (cvec a1 a2 a3 a4) hc F2 := by
    rw [EL_apply_of_inr _ hc F2 (by simp [F2, mkV, ex, Pi.single_apply]), bM_F2, hF2', add_comm]
  simp only [map_add, map_smul, hγe0, hγf0, hγE1, hγE2, hγF1, hγF2]

end CFSG.Quasithin.H13.C1294.Model

end
