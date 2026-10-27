module

public import CFSG.Quasithin.MS93.S5A56W2

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F] [CharP F 2]

@[expose] def xWo (F : Type) [Field F] : Sp4 F :=
  transv (e₂ F) 1 * transv (e₁ F + f₁ F + f₂ F) 1

theorem xWo_mulVec (v : V4 F) :
    mat (xWo F) *ᵥ v = (v (.inl 1) + v (.inr 0)) • e₁ F +
      (v (.inl 0) + v (.inr 0) + v (.inr 1)) • e₂ F + (v (.inl 0) + v (.inl 1)) • f₁ F +
      (v (.inl 0) + v (.inl 1) + v (.inr 0) + v (.inr 1)) • f₂ F := by
  rw [xWo, mat_mul_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq] <;> grind

omit [CharP F 2] in
theorem map_inv_inf_eq_bot_of {g : Sp4 F} {W W' : Submodule F (V4 F)}
    (h : ∀ v ∈ W', mat g *ᵥ v ∈ W → v = 0) : W.map (mulVecLin (mat g⁻¹)) ⊓ W' = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  rw [mem_map_mulVecLin, inv_inv] at hv1
  exact (Submodule.mem_bot F).2 (h v hv2 hv1)

theorem xWo_opp : (ln₀' F).map (mulVecLin (mat (xWo F)⁻¹)) ⊓ ln₀' F = ⊥ := by
  refine map_inv_inf_eq_bot fun v hv hv' => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀'.1 hv
  obtain ⟨h2, h3⟩ := mem_ln₀'.1 hv'
  rw [xWo_mulVec] at h2 h3
  simp [h0, h1] at h2 h3
  have h4 : v (.inr 1) = 0 := by rw [h2, zero_add] at h3; exact h3
  exact ext4 (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h4])

theorem xWo_opp_ln₀ : (ln₀' F).map (mulVecLin (mat (xWo F)⁻¹)) ⊓ ln₀ F = ⊥ := by
  refine map_inv_inf_eq_bot_of fun v hv hv' => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  obtain ⟨h2, h3⟩ := mem_ln₀'.1 hv'
  rw [xWo_mulVec] at h2 h3
  simp [h0, h1] at h2 h3
  exact ext4 (by simp [h3]) (by simp [h2]) (by simp [h0]) (by simp [h1])

theorem xWo_mem_commutator [Finite F] : xWo F ∈ commutator (Sp4 F) :=
  transv_mul_transv_mem_commutator e₂_ne_zero (fun h => by simpa using congrFun h (.inl 0))
    one_ne_zero one_ne_zero

section W2o

private theorem ttv_f2_f1_e2f1f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₂ F + f₁ F + f₂ F) = e₂ F + f₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1_e1f1f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₁ F + f₁ F + f₂ F) = e₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1_e1e2 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₁ F + e₂ F) = e₁ F + e₂ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1_e2 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₂ F) = e₂ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1_e1 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₁ F) = e₁ F + f₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1f2_e2f1f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₂ F + f₁ F + f₂ F) = e₂ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1f2_e1f1f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₁ F + f₁ F + f₂ F) = e₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1f2_e2f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₂ F + f₂ F) = e₂ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1f2_e1e2 :
    mat (transv (f₂ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₁ F + e₂ F) = e₁ F + e₂ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1_e2f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₂ F + f₂ F) = e₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_f2_f1_e1e2f2 :
    mat (transv (f₂ F) 1 * transv (f₁ F) 1) *ᵥ (e₁ F + e₂ F + f₂ F) = e₁ F + e₂ F + f₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_e2f2_e1f1f2_e2f2 :
    mat (transv (e₂ F + f₂ F) 1 * transv (e₁ F + f₁ F + f₂ F) 1) *ᵥ (e₂ F + f₂ F) =
      e₁ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem ttv_e2f2_e1f1f2_e2f1 :
    mat (transv (e₂ F + f₂ F) 1 * transv (e₁ F + f₁ F + f₂ F) 1) *ᵥ (e₂ F + f₁ F) =
      f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem w2o_generators {H J : Subgroup (Sp4 F)}
    (hH : J.map (MulAut.conj (sig F)).toMonoidHom ⊔ J ⊔
      J.map (MulAut.conj (xWo F)).toMonoidHom ≤ H)
    (h₁ : transv (e₁ F) 1 * transv (e₂ F) 1 ∈ J)
    (h₂ : transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J) :
    transv (e₁ F) 1 * transv (e₂ F) 1 ∈ H ∧ transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ H ∧
      transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1 ∈ H ∧ transv (f₂ F) 1 * transv (f₁ F) 1 ∈ H ∧
      transv (f₂ F) 1 * transv (f₁ F + f₂ F) 1 ∈ H ∧
      transv (f₁ F) 1 * transv (f₁ F + f₂ F) 1 ∈ H ∧
      transv (e₂ F + f₁ F + f₂ F) 1 * transv (e₁ F + f₁ F + f₂ F) 1 ∈ H ∧
      transv (e₂ F + f₁ F + f₂ F) 1 * transv (e₁ F + e₂ F) 1 ∈ H ∧
      transv (e₁ F + f₁ F + f₂ F) 1 * transv (e₁ F + e₂ F) 1 ∈ H := by
  have hJ : J ≤ H := (le_sup_right.trans le_sup_left).trans hH
  have hS : ∀ {a b : V4 F}, transv a 1 * transv b 1 ∈ J →
      transv (mat (sig F) *ᵥ a) 1 * transv (mat (sig F) *ᵥ b) 1 ∈ H := fun hab =>
    hH (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, hab, by
      change sig F * _ * (sig F)⁻¹ = _
      rw [conj_transv_mul_transv]⟩))
  have hX : ∀ {a b : V4 F}, transv a 1 * transv b 1 ∈ J →
      transv (mat (xWo F) *ᵥ a) 1 * transv (mat (xWo F) *ᵥ b) 1 ∈ H := fun hab =>
    hH (Subgroup.mem_sup_right ⟨_, hab, by
      change xWo F * _ * (xWo F)⁻¹ = _
      rw [conj_transv_mul_transv]⟩)
  have h₃ : transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J :=
    transv_mul_transv_trans (transv_mul_transv_symm h₁) h₂
  have s12 : mat (sig F) *ᵥ (e₁ F + e₂ F) = f₁ F + f₂ F := by
    rw [mulVec_add, sig_mulVec_e₁, sig_mulVec_e₂, add_comm]
  have x1 : mat (xWo F) *ᵥ e₁ F = e₂ F + f₁ F + f₂ F := by
    rw [xWo_mulVec]; refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have x2 : mat (xWo F) *ᵥ e₂ F = e₁ F + f₁ F + f₂ F := by
    rw [xWo_mulVec]; refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have x12 : mat (xWo F) *ᵥ (e₁ F + e₂ F) = e₁ F + e₂ F := by
    rw [xWo_mulVec]; refine ext4 ?_ ?_ ?_ ?_ <;> simp [CharTwo.add_self_eq_zero]
  refine ⟨hJ h₁, hJ h₂, hJ h₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hS h₁; rwa [sig_mulVec_e₁, sig_mulVec_e₂] at this
  · have := hS h₂; rwa [sig_mulVec_e₁, s12] at this
  · have := hS h₃; rwa [sig_mulVec_e₂, s12] at this
  · have := hX h₁; rwa [x1, x2] at this
  · have := hX h₂; rwa [x1, x12] at this
  · have := hX h₃; rwa [x2, x12] at this

theorem commutator_le_sup_w2o (hq : Nat.card F = 2) {J : Subgroup (Sp4 F)}
    (h₁ : transv (e₁ F) 1 * transv (e₂ F) 1 ∈ J)
    (h₂ : transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J) :
    commutator (Sp4 F) ≤ J.map (MulAut.conj (sig F)).toMonoidHom ⊔ J ⊔
      J.map (MulAut.conj (xWo F)).toMonoidHom := by
  set H := J.map (MulAut.conj (sig F)).toMonoidHom ⊔ J ⊔ J.map (MulAut.conj (xWo F)).toMonoidHom
  obtain ⟨g₁, g₂, g₃, dS₁, dS₂, dS₃, dX₁, dX₂, dX₃⟩ := w2o_generators le_rfl h₁ h₂
  have hT := fun {a b c : V4 F} => @transv_mul_transv_trans F _ _ H a b c
  have hY := fun {a b : V4 F} => @transv_mul_transv_symm F _ _ H a b
  have hC := fun {a b x y a' b' : V4 F} => @transv_mul_transv_conj F _ H a b x y a' b'
  have c1 := hC dX₁ dS₁ ttv_f2_f1_e2f1f2 ttv_f2_f1_e1f1f2
  have c2 := hC dX₂ dS₁ ttv_f2_f1_e2f1f2 ttv_f2_f1_e1e2
  have c3 := hC (hT dX₂ (hY g₃)) dS₁ ttv_f2_f1_e2f1f2 ttv_f2_f1_e2
  have c4 := hC (hT dX₂ (hY g₂)) dS₁ ttv_f2_f1_e2f1f2 ttv_f2_f1_e1
  have c5 := hC dX₁ dS₂ ttv_f2_f1f2_e2f1f2 ttv_f2_f1f2_e1f1f2
  have c6 := hC (hT c5 g₂) dS₂ ttv_f2_f1f2_e2f2 ttv_f2_f1f2_e1e2
  have c7 := hC (hT (hT (hT c5 g₂) (hY dX₂)) c6) dS₁ ttv_f2_f1_e2f2 ttv_f2_f1_e1e2f2
  have c8 := hC (hY c3) (hT (hT c5 g₂) (hY dX₃)) ttv_e2f2_e1f1f2_e2f2 ttv_e2f2_e1f1f2_e2f1
  have d1 := hT g₂ (hY dX₃)
  have d2 := hT (hY c5) (hY c3)
  have hall : ∀ u : V4 F, u ≠ 0 → transv (e₁ F) 1 * transv u 1 ∈ H :=
    forall_ne_zero_of_card_two hq (transv_mul_transv_self_mem H _) g₁ (hT (hT d1 c8) (hY dS₃))
      (hT (hT d1 c8) (hY dS₂)) g₂ (hT d2 c4) (hT d2 c1) d2 (hY c5) (hT d1 c8) (hT g₁ c7)
      (hT (hT g₂ (hY dX₂)) c6) d1 (hT g₂ (hY dX₂)) (hT d2 c2)
  refine (commutator_le_closure_transv_mul hq).trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨u, v, hu, hv, rfl⟩
  exact hT (hY (hall u hu)) (hall v hv)

end W2o

end CFSG.Quasithin.MS93.S5
