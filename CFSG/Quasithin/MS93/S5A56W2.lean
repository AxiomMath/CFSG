module

public import CFSG.Quasithin.MS93.S5A56Sp
public import CFSG.Quasithin.MS93.MSPOrd3

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem commutator_le_closure_transv_mul (hq : Nat.card F = 2) :
    commutator (Sp4 F) ≤ Subgroup.closure {g | ∃ u v : V4 F, u ≠ 0 ∧ v ≠ 0 ∧
      g = transv u 1 * transv v 1} := by
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hq
  set S := Subgroup.closure {g | ∃ u v : V4 F, u ≠ 0 ∧ v ≠ 0 ∧ g = transv u 1 * transv v 1}
  intro g hg
  rw [mem_commutator_iff_sign c] at hg
  have hgσ : g = B5FinSp.theta c ((B5FinSp.theta c).symm g) := by simp
  rw [hgσ]
  have hσ : (B5FinSp.theta c).symm g ∈ alternatingGroup (Fin 6) := hg
  suffices hind : ∀ (n : ℕ) (l : List (Equiv.Perm (Fin 6))), (∀ σ ∈ l, σ.IsSwap) →
      l.length = 2 * n → B5FinSp.theta c l.prod ∈ S by
    obtain ⟨l, hl, hls⟩ := Equiv.Perm.truncSwapFactors ((B5FinSp.theta c).symm g)
    rw [← hl] at hσ ⊢
    obtain ⟨n, hn⟩ := (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length hls).1 hσ
    exact hind n l hls (by rw [hn]; ring)
  intro n
  induction n with
  | zero =>
    intro l _ hl
    rw [List.length_eq_zero_iff.1 hl, List.prod_nil, map_one]
    exact one_mem _
  | succ n ih =>
    intro l hl hn
    obtain ⟨a, l, rfl⟩ := l.exists_of_length_succ (n := 2 * n + 1) (by rw [hn]; ring)
    rw [List.length_cons] at hn
    obtain ⟨b, l, rfl⟩ := l.exists_of_length_succ (n := 2 * n) (by omega)
    rw [List.length_cons] at hn
    rw [List.prod_cons, List.prod_cons, ← mul_assoc, map_mul, map_mul]
    obtain ⟨u, hu, hau⟩ := exists_theta_eq_transv c (hl a (by simp))
    obtain ⟨v, hv, hbv⟩ := exists_theta_eq_transv c (hl b (by simp))
    refine mul_mem (Subgroup.subset_closure ⟨u, v, hu, hv, by rw [hau, hbv]⟩)
      (ih l (fun σ hσ => hl σ (by simp [hσ])) (by omega))

@[expose] def xW (F : Type) [Field F] : Sp4 F := transv (e₂ F) 1 * transv (e₁ F + f₂ F) 1

theorem xW_mulVec (v : V4 F) :
    mat (xW F) *ᵥ v = (v (.inl 0) + v (.inl 1) + v (.inr 0)) • e₁ F +
      (v (.inr 0) + v (.inr 1)) • e₂ F + v (.inr 0) • f₁ F +
      (v (.inl 1) + v (.inr 0) + v (.inr 1)) • f₂ F := by
  rw [xW, mat_mul_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq] <;> grind

theorem xW_opp : (ln₀' F).map (mulVecLin (mat (xW F)⁻¹)) ⊓ ln₀' F = ⊥ := by
  refine map_inv_inf_eq_bot fun v hv hv' => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀'.1 hv
  obtain ⟨h2, h3⟩ := mem_ln₀'.1 hv'
  rw [xW_mulVec] at h2 h3
  simp [h0, h1] at h2 h3
  have h4 : v (.inr 1) = 0 := by rw [h2, zero_add] at h3; exact h3
  exact ext4 (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h4])

variable [Finite F]

theorem xW_mem_commutator : xW F ∈ commutator (Sp4 F) :=
  transv_mul_transv_mem_commutator e₂_ne_zero (fun h => by simpa using congrFun h (.inl 0))
    one_ne_zero one_ne_zero

section Pairs

omit [Finite F] in
theorem transv_mul_transv_symm {H : Subgroup (Sp4 F)} {a b : V4 F}
    (h : transv a 1 * transv b 1 ∈ H) : transv b 1 * transv a 1 ∈ H := by
  have := inv_mem h
  rwa [_root_.mul_inv_rev, transv_inv, transv_inv, CharTwo.neg_eq] at this

omit [Finite F] in
theorem transv_mul_transv_trans {H : Subgroup (Sp4 F)} {a b c : V4 F}
    (hab : transv a 1 * transv b 1 ∈ H) (hbc : transv b 1 * transv c 1 ∈ H) :
    transv a 1 * transv c 1 ∈ H := by
  have := mul_mem hab hbc
  rwa [show transv a 1 * transv b 1 * (transv b 1 * transv c 1) =
    transv a 1 * (transv b 1 * transv b 1) * transv c 1 by group, transv_mul,
    CharTwo.add_self_eq_zero, transv_zero, mul_one] at this

omit [Finite F] [CharP F 2] in
theorem transv_mul_transv_conj {H : Subgroup (Sp4 F)} {a b x y a' b' : V4 F}
    (hab : transv a 1 * transv b 1 ∈ H) (hxy : transv x 1 * transv y 1 ∈ H)
    (ha : mat (transv x 1 * transv y 1) *ᵥ a = a') (hb : mat (transv x 1 * transv y 1) *ᵥ b = b') :
    transv a' 1 * transv b' 1 ∈ H := by
  have := mul_mem (mul_mem hxy hab) (inv_mem hxy)
  rwa [conj_transv_mul_transv, ha, hb] at this

omit [Finite F] in
theorem transv_mul_transv_self_mem (H : Subgroup (Sp4 F)) (a : V4 F) :
    transv a 1 * transv a 1 ∈ H := by
  rw [transv_mul, CharTwo.add_self_eq_zero, transv_zero]
  exact one_mem H

end Pairs

section W2

omit [Finite F] in
private theorem ttv_e1_e1f2_e2 :
    mat (transv (e₁ F) 1 * transv (e₁ F + f₂ F) 1) *ᵥ (e₂ F) = e₁ F + e₂ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_e1f2_e1 :
    mat (transv (e₁ F) 1 * transv (e₁ F + f₂ F) 1) *ᵥ (e₁ F) = e₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_f1_f1f2_e2 :
    mat (transv (f₁ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₂ F) = e₂ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_f1_f1f2_e1 :
    mat (transv (f₁ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₁ F) = e₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_f2_f2 :
    mat (transv (e₁ F) 1 * transv (f₂ F) 1) *ᵥ (f₂ F) = f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_f2_f1 :
    mat (transv (e₁ F) 1 * transv (f₂ F) 1) *ᵥ (f₁ F) = e₁ F + f₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_f2_e2 :
    mat (transv (e₁ F) 1 * transv (f₂ F) 1) *ᵥ (e₂ F) = e₂ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_f2_e1 :
    mat (transv (e₁ F) 1 * transv (f₂ F) 1) *ᵥ (e₁ F) = e₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1f2_f2_f2 :
    mat (transv (e₁ F + f₂ F) 1 * transv (f₂ F) 1) *ᵥ (f₂ F) = f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1f2_f2_f1 :
    mat (transv (e₁ F + f₂ F) 1 * transv (f₂ F) 1) *ᵥ (f₁ F) = e₁ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_f1_f1f2_e1e2f2 :
    mat (transv (f₁ F) 1 * transv (f₁ F + f₂ F) 1) *ᵥ (e₁ F + e₂ F + f₂ F) =
      e₁ F + e₂ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e2_e1e2_f2 :
    mat (transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1) *ᵥ (f₂ F) = e₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e2_e1e2_f1 :
    mat (transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1) *ᵥ (f₁ F) = e₁ F + e₂ F + f₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_e2_f2 :
    mat (transv (e₁ F) 1 * transv (e₂ F) 1) *ᵥ (f₂ F) = e₂ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_e2_f1f2 :
    mat (transv (e₁ F) 1 * transv (e₂ F) 1) *ᵥ (f₁ F + f₂ F) = e₁ F + e₂ F + f₁ F + f₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_f2_e2f2 :
    mat (transv (e₁ F) 1 * transv (f₂ F) 1) *ᵥ (e₂ F + f₂ F) = e₂ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem ttv_e1_f2_e1e2f1f2 :
    mat (transv (e₁ F) 1 * transv (f₂ F) 1) *ᵥ (e₁ F + e₂ F + f₁ F + f₂ F) = e₂ F + f₁ F := by
  rw [transv_mul_transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [CharP F 2] [Finite F] in
theorem forall_ne_zero_of_card_two (hq : Nat.card F = 2) {P : V4 F → Prop}
    (h1 : P (e₁ F)) (h2 : P (e₂ F)) (h3 : P (f₁ F)) (h4 : P (f₂ F)) (h5 : P (e₁ F + e₂ F))
    (h6 : P (e₁ F + f₁ F)) (h7 : P (e₁ F + f₂ F)) (h8 : P (e₂ F + f₁ F)) (h9 : P (e₂ F + f₂ F))
    (h10 : P (f₁ F + f₂ F)) (h11 : P (e₁ F + e₂ F + f₁ F)) (h12 : P (e₁ F + e₂ F + f₂ F))
    (h13 : P (e₁ F + f₁ F + f₂ F)) (h14 : P (e₂ F + f₁ F + f₂ F))
    (h15 : P (e₁ F + e₂ F + f₁ F + f₂ F)) (u : V4 F) (hu : u ≠ 0) : P u := by
  have h01 := eq_zero_or_eq_one_of_card_two hq
  have hu' : u = u (.inl 0) • e₁ F + u (.inl 1) • e₂ F + u (.inr 0) • f₁ F +
      u (.inr 1) • f₂ F := by
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  rw [hu'] at hu ⊢
  generalize u (.inl 0) = a at hu ⊢
  generalize u (.inl 1) = b at hu ⊢
  generalize u (.inr 0) = c at hu ⊢
  generalize u (.inr 1) = d at hu ⊢
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
    rcases h01 c with rfl | rfl <;> rcases h01 d with rfl | rfl <;>
    simp only [zero_smul, one_smul, add_zero, zero_add] at hu ⊢
  exacts [absurd rfl hu, h4, h3, h10, h2, h9, h8, h14, h1, h7, h6, h13, h5, h12, h11, h15]

omit [Finite F] in
theorem w2_generators {H J : Subgroup (Sp4 F)}
    (hH : J.map (MulAut.conj (sig F)).toMonoidHom ⊔ J ⊔
      J.map (MulAut.conj (xW F)).toMonoidHom ≤ H)
    (h₁ : transv (e₁ F) 1 * transv (e₂ F) 1 ∈ J)
    (h₂ : transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J) :
    transv (e₁ F) 1 * transv (e₂ F) 1 ∈ H ∧ transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ H ∧
      transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1 ∈ H ∧ transv (f₂ F) 1 * transv (f₁ F) 1 ∈ H ∧
      transv (f₂ F) 1 * transv (f₁ F + f₂ F) 1 ∈ H ∧
      transv (f₁ F) 1 * transv (f₁ F + f₂ F) 1 ∈ H ∧ transv (e₁ F) 1 * transv (f₂ F) 1 ∈ H ∧
      transv (e₁ F) 1 * transv (e₁ F + f₂ F) 1 ∈ H ∧
      transv (e₁ F + f₂ F) 1 * transv (f₂ F) 1 ∈ H := by
  have hJ : J ≤ H := (le_sup_right.trans le_sup_left).trans hH
  have hS : ∀ {a b : V4 F}, transv a 1 * transv b 1 ∈ J →
      transv (mat (sig F) *ᵥ a) 1 * transv (mat (sig F) *ᵥ b) 1 ∈ H := fun hab =>
    hH (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, hab, by
      change sig F * _ * (sig F)⁻¹ = _
      rw [conj_transv_mul_transv]⟩))
  have hX : ∀ {a b : V4 F}, transv a 1 * transv b 1 ∈ J →
      transv (mat (xW F) *ᵥ a) 1 * transv (mat (xW F) *ᵥ b) 1 ∈ H := fun hab =>
    hH (Subgroup.mem_sup_right ⟨_, hab, by
      change xW F * _ * (xW F)⁻¹ = _
      rw [conj_transv_mul_transv]⟩)
  have h₃ : transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J :=
    transv_mul_transv_trans (transv_mul_transv_symm h₁) h₂
  have s12 : mat (sig F) *ᵥ (e₁ F + e₂ F) = f₁ F + f₂ F := by
    rw [mulVec_add, sig_mulVec_e₁, sig_mulVec_e₂, add_comm]
  have x1 : mat (xW F) *ᵥ e₁ F = e₁ F := by
    rw [xW_mulVec]; refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have x2 : mat (xW F) *ᵥ e₂ F = e₁ F + f₂ F := by
    rw [xW_mulVec]; refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have x12 : mat (xW F) *ᵥ (e₁ F + e₂ F) = f₂ F := by
    rw [xW_mulVec]; refine ext4 ?_ ?_ ?_ ?_ <;> simp [CharTwo.add_self_eq_zero]
  refine ⟨hJ h₁, hJ h₂, hJ h₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hS h₁; rwa [sig_mulVec_e₁, sig_mulVec_e₂] at this
  · have := hS h₂; rwa [sig_mulVec_e₁, s12] at this
  · have := hS h₃; rwa [sig_mulVec_e₂, s12] at this
  · have := hX h₂; rwa [x1, x12] at this
  · have := hX h₁; rwa [x1, x2] at this
  · have := hX h₃; rwa [x2, x12] at this

omit [Finite F] in
theorem commutator_le_sup_w2 (hq : Nat.card F = 2) {J : Subgroup (Sp4 F)}
    (h₁ : transv (e₁ F) 1 * transv (e₂ F) 1 ∈ J)
    (h₂ : transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J) :
    commutator (Sp4 F) ≤ J.map (MulAut.conj (sig F)).toMonoidHom ⊔ J ⊔
      J.map (MulAut.conj (xW F)).toMonoidHom := by
  set H := J.map (MulAut.conj (sig F)).toMonoidHom ⊔ J ⊔ J.map (MulAut.conj (xW F)).toMonoidHom
  obtain ⟨g₁, g₂, g₃, d3, d4, d7, d5, d6, d8⟩ := w2_generators le_rfl h₁ h₂
  have hT := fun {a b c : V4 F} => @transv_mul_transv_trans F _ _ H a b c
  have hY := fun {a b : V4 F} => @transv_mul_transv_symm F _ _ H a b
  have hC := fun {a b x y a' b' : V4 F} => @transv_mul_transv_conj F _ H a b x y a' b'
  have d1 := hY g₁
  have c1 := hC d1 d6 ttv_e1_e1f2_e2 ttv_e1_e1f2_e1
  have c2 := hC d1 d7 ttv_f1_f1f2_e2 ttv_f1_f1f2_e1
  have c3 := hC d3 d5 ttv_e1_f2_f2 ttv_e1_f2_f1
  have c4 := hC d1 d5 ttv_e1_f2_e2 ttv_e1_f2_e1
  have c5 := hC d3 d8 ttv_e1f2_f2_f2 ttv_e1f2_f2_f1
  have c6 := hC c1 d7 ttv_f1_f1f2_e1e2f2 ttv_f1_f1f2_e1
  have c7 := hC d3 g₃ ttv_e2_e1e2_f2 ttv_e2_e1e2_f1
  have c8 := hC d4 g₁ ttv_e1_e2_f2 ttv_e1_e2_f1f2
  have c9 := hC c8 d5 ttv_e1_f2_e2f2 ttv_e1_f2_e1e2f1f2
  have hall : ∀ u : V4 F, u ≠ 0 → transv (e₁ F) 1 * transv u 1 ∈ H :=
    forall_ne_zero_of_card_two hq (transv_mul_transv_self_mem H _) g₁ (hT d5 d3) d5 g₂ (hT d5 c3)
      d6 (hT g₁ c9) (hY c4) (hT d5 d4) (hT d6 c7) (hY c1) (hT d5 c5) (hT d6 (hY c2))
      (hT d6 (hY c6))
  refine (commutator_le_closure_transv_mul hq).trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨u, v, hu, hv, rfl⟩
  exact hT (hY (hall u hu)) (hall v hv)

end W2

end CFSG.Quasithin.MS93.S5
