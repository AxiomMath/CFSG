module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelW2

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def Hm : Subgroup (VM ≃ₗ[ZMod 2] VM) where
  carrier := {γ | γ ∈ GM ∧ γ e0 = e0}
  mul_mem' := fun {a b} ha hb => ⟨GM.mul_mem ha.1 hb.1, by
    show a (b e0) = e0
    rw [hb.2, ha.2]⟩
  one_mem' := ⟨GM.one_mem, rfl⟩
  inv_mem' := fun {a} ha => ⟨GM.inv_mem ha.1, by
    show a.symm e0 = e0
    rw [LinearEquiv.symm_apply_eq]
    exact ha.2.symm⟩

theorem mem_Hm_iff (γ : VM ≃ₗ[ZMod 2] VM) : γ ∈ Hm ↔ γ ∈ GM ∧ γ e0 = e0 := Iff.rfl

theorem bM_self_eq_zero : ∀ u : VM, bM u u = 0 := by decide +kernel

theorem bM_smul_right (x u : VM) (a : ZMod 2) : bM x (a • u) = a * bM x u := by
  rw [bM_symm, bM_smul_left, bM_symm]

theorem zmod2_sq_add_sq : ∀ l : ZMod 2, l * l + l * l = 0 := by decide

@[expose] def trv (u : VM) : VM ≃ₗ[ZMod 2] VM where
  toFun x := x + bM x u • u
  invFun x := x + bM x u • u
  map_add' x y := by
    show (x + y) + bM (x + y) u • u = (x + bM x u • u) + (y + bM y u • u)
    rw [bM_add_left, add_smul]
    abel
  map_smul' a x := by
    show a • x + bM (a • x) u • u = a • (x + bM x u • u)
    rw [bM_smul_left, smul_add, mul_smul]
  left_inv x := by
    show (x + bM x u • u) + bM (x + bM x u • u) u • u = x
    rw [bM_add_left, bM_smul_left, bM_self_eq_zero, mul_zero, add_zero, add_assoc, ← add_smul,
      zmod2_self_add_self, zero_smul, add_zero]
  right_inv x := by
    show (x + bM x u • u) + bM (x + bM x u • u) u • u = x
    rw [bM_add_left, bM_smul_left, bM_self_eq_zero, mul_zero, add_zero, add_assoc, ← add_smul,
      zmod2_self_add_self, zero_smul, add_zero]

theorem trv_mem_GM {u : VM} (hu : qM u = 1) : trv u ∈ GM := by
  intro x
  show qM (x + bM x u • u) = qM x
  rw [qM_add, qM_smul, hu, bM_smul_right, mul_one, add_assoc, zmod2_sq_add_sq, add_zero]

theorem trv_mem_Hm {u : VM} (hu : qM u = 1) (hu0 : u (Sum.inr 0) = 0) : trv u ∈ Hm := by
  refine ⟨trv_mem_GM hu, ?_⟩
  show e0 + bM e0 u • u = e0
  rw [bM_e0_left, hu0, zero_smul, add_zero]

theorem projU_of_inr_zero (v : VM) (hv : v (Sum.inr 0) = 0) :
    projU v = v - v (Sum.inl 0) • e0 := by
  unfold projU
  simp [hv]

theorem projU_sub_smul : ∀ (v : VM) (a : ZMod 2), projU (v - a • e0) = projU v := by
  decide +kernel

theorem qM_projU_aux : ∀ v : VM, v (Sum.inr 0) = 0 →
    qM (v - v (Sum.inl 0) • e0) = qM v := by
  decide +kernel

theorem projU_of_inU : ∀ v : VM, inU v → projU v = v := by
  decide +kernel

theorem qM_projU {v : VM} (hv : v (Sum.inr 0) = 0) : qM (projU v) = qM v := by
  rw [projU_of_inr_zero v hv]
  exact qM_projU_aux v hv

theorem projU_comp {g : VM ≃ₗ[ZMod 2] VM} (hg : g ∈ Hm) (w : VM) (hw : w (Sum.inr 0) = 0) :
    projU (g (projU w)) = projU (g w) := by
  rw [projU_of_inr_zero w hw]
  have h1 : g (w - w (Sum.inl 0) • e0) = g w - w (Sum.inl 0) • e0 := by
    rw [map_sub g, map_smul g, hg.2]
    rfl
  rw [h1]
  exact projU_sub_smul (g w) (w (Sum.inl 0))

@[expose] def TX : Type := {c : VM // inU c ∧ qM c = 0 ∧ c ≠ 0}

instance : Fintype TX := Subtype.fintype _

theorem card_TX : Fintype.card TX = 9 := by
  decide +kernel

theorem inr_zero_of_Hm {g : VM ≃ₗ[ZMod 2] VM} (hg : g ∈ Hm) (c : TX) :
    (g c.1) (Sum.inr 0) = 0 := by
  have hc := c.2.1
  rw [← bM_e0_right (g c.1), ← hg.2, bM_of_GM hg.1, bM_e0_right]
  exact hc.2

theorem act_TX_mem {g : VM ≃ₗ[ZMod 2] VM} (hg : g ∈ Hm) (c : TX) :
    inU (projU (g c.1)) ∧ qM (projU (g c.1)) = 0 ∧ projU (g c.1) ≠ 0 := by
  obtain ⟨hc, hqc, hc0⟩ := c.2
  have hgr := inr_zero_of_Hm hg c
  refine ⟨inU_projU _, ?_, ?_⟩
  · rw [qM_projU hgr, hg.1 c.1, hqc]
  · intro h0
    rw [projU_of_inr_zero _ hgr, sub_eq_zero] at h0
    have hgs : g.symm e0 = e0 := by
      rw [LinearEquiv.symm_apply_eq]
      exact hg.2.symm
    have hc' : c.1 = (g c.1 (Sum.inl 0)) • e0 := by
      have := congrArg g.symm h0
      rw [LinearEquiv.symm_apply_apply, map_smul, hgs] at this
      exact this
    have h1 : c.1 (Sum.inl 0) = g c.1 (Sum.inl 0) := by
      conv_lhs => rw [hc']
      simp [e0, mkV, ex, Pi.single_apply]
    have ha0 : g c.1 (Sum.inl 0) = 0 := by
      rw [← h1]
      exact hc.1
    apply hc0
    rw [hc', ha0, zero_smul]

instance : MulAction Hm TX where
  smul g c := ⟨projU (g.1 c.1), act_TX_mem g.2 c⟩
  one_smul c := Subtype.ext (by
    show projU ((1 : VM ≃ₗ[ZMod 2] VM) c.1) = c.1
    exact projU_of_inU _ c.2.1)
  mul_smul g h c := Subtype.ext (by
    show projU ((g.1 * h.1) c.1) = projU (g.1 (projU (h.1 c.1)))
    rw [projU_comp g.2 _ (inr_zero_of_Hm h.2 c), LinearEquiv.mul_apply])

theorem TX_smul_val (g : Hm) (c : TX) : (g • c).1 = projU (g.1 c.1) := rfl

end CFSG.Quasithin.H13.C1294.Model

end
