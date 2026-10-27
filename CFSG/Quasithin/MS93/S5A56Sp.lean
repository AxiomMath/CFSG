module

public import CFSG.Quasithin.MS93.MSPGen3
public import CFSG.Quasithin.MS93.MSPSix
public import CFSG.Quasithin.MS93.S5AGeo2
public import CFSG.ClassicalGroups.Symplectic.Perfect

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

section Commutator

theorem isPerfect_sp4_of_card (hF : 4 ≤ Nat.card F) : Group.IsPerfect (Sp4 F) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin 2 F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F 2 (Or.inl (Or.inr hF))
  let e : TauCeti.GLSymplecticFin 2 F ≃* StatedSp 2 F :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 F).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := 2) (K := F)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

variable [Finite F] [CharP F 2]

theorem card_eq_two_or_four_le : Nat.card F = 2 ∨ 4 ≤ Nat.card F := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
  · left
    have : (n : ℕ) = 1 := by have := n.pos; omega
    rw [this, pow_one]
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem transv_mul_transv_mem_commutator {u v : V4 F} (hu : u ≠ 0) (hv : v ≠ 0) {c d : F}
    (hc : c ≠ 0) (hd : d ≠ 0) : transv u c * transv v d ∈ commutator (Sp4 F) := by
  rcases card_eq_two_or_four_le (F := F) with h2 | h4
  · obtain ⟨e⟩ := nonempty_ringEquiv_of_card_two h2
    rw [Subgroup.mul_mem_iff_of_index_two (index_commutator e)]
    exact iff_of_false (transv_not_mem_commutator_of_card_two h2 hu c hc)
      (transv_not_mem_commutator_of_card_two h2 hv d hd)
  · have := isPerfect_sp4_of_card h4
    exact Group.IsPerfect.mem_commutator

end Commutator

section Elements

variable [CharP F 2]

@[expose] noncomputable def sig (F : Type) [Field F] [CharP F 2] : Sp4 F := jSwap F * wAlpha F

theorem sig_mulVec (v : V4 F) :
    mat (sig F) *ᵥ v = v (.inr 1) • e₁ F + v (.inr 0) • e₂ F + v (.inl 1) • f₁ F +
      v (.inl 0) • f₂ F := by
  rw [sig, mat_mul_mulVec, wAlpha_mulVec, jSwap_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem sig_mul_self : sig F * sig F = 1 := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, sig_mulVec, sig_mulVec, mat_one, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem sig_inv : (sig F)⁻¹ = sig F := inv_eq_of_mul_eq_one_right sig_mul_self

@[expose] def xAlt (F : Type) [Field F] : Sp4 F :=
  transv (e₁ F) 1 * transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1

theorem xAlt_mulVec (v : V4 F) :
    mat (xAlt F) *ᵥ v = v + v (.inr 1) • e₁ F + v (.inr 0) • e₂ F := by
  rw [xAlt, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply] <;> grind

@[expose] def wAl (F : Type) [Field F] : Sp4 F :=
  transv (e₁ F + e₂ F) 1 * transv (f₁ F + f₂ F) 1 * transv (e₁ F + e₂ F + f₁ F + f₂ F) 1

theorem wAl_mulVec (v : V4 F) :
    mat (wAl F) *ᵥ v = v (.inl 1) • e₁ F + v (.inl 0) • e₂ F + v (.inr 1) • f₁ F +
      v (.inr 0) • f₂ F := by
  rw [wAl, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply] <;> grind

@[expose] def nuE (a : F) : Sp4 F := transv (f₂ F + e₁ F) a * transv (f₂ F) a * transv (e₁ F) a

theorem nuE_mulVec (a : F) (v : V4 F) :
    mat (nuE a) *ᵥ v = v + (a * v (.inl 1)) • e₁ F + (a * v (.inr 0)) • f₂ F := by
  rw [nuE, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply] <;> grind

end Elements

section Weyl

variable [CharP F 2]

theorem weyl_mulVec {a b : V4 F} (hab : form F a b = 1) {c : F} (hc : c ≠ 0) :
    mat (transv a c⁻¹ * transv b c * transv a c⁻¹) *ᵥ a = c • b := by
  have hba : form F b a = 1 := by rw [form_swap, hab, CharTwo.neg_eq]
  have hf : form F a (a + (c * 1) • b) = c := by
    rw [map_add, map_smul, form_self, hab, smul_eq_mul]
    ring
  have h1 : mat (transv a c⁻¹) *ᵥ a = a := by
    rw [transv_mulVec, form_self, mul_zero, zero_smul, add_zero]
  have h2 : mat (transv b c) *ᵥ a = a + (c * 1) • b := by rw [transv_mulVec, hba]
  rw [mat_mul_mulVec, mat_mul_mulVec, h1, h2, transv_mulVec, hf, inv_mul_cancel₀ hc, one_smul,
    mul_one, add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem transv_mem_of_weyl {H : Subgroup (Sp4 F)} {a b : V4 F} (hab : form F a b = 1)
    (ha : ∀ s, transv a s ∈ H) {c : F} (hc : c ≠ 0) (hb : transv b c ∈ H) (d : F) :
    transv b d ∈ H := by
  have hw : transv a c⁻¹ * transv b c * transv a c⁻¹ ∈ H :=
    mul_mem (mul_mem (ha _) hb) (ha _)
  have h1 := mul_mem (mul_mem hw (ha (d / c ^ 2))) (inv_mem hw)
  rw [transv_conj, weyl_mulVec hab hc, transv_smul_vec] at h1
  convert h1 using 2
  field_simp

end Weyl

section Std

variable [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem f₂_mem_ln₀' : f₂ F ∈ ln₀' F := Submodule.subset_span (by simp)

omit [Finite F] [CharP F 2] in
theorem f₁_mem_ln₀' : f₁ F ∈ ln₀' F := Submodule.subset_span (by simp)

omit [Finite F] [CharP F 2] in
theorem span_f₁_ne_span_f₂ : (F ∙ f₁ F) ≠ (F ∙ f₂ F) := by
  intro h
  have : f₁ F ∈ F ∙ f₂ F := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  have := congrFun hc (.inr 0)
  simp at this

omit [Finite F] [CharP F 2] in
theorem xPoint_f₂_sup_f₁_le : xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) ≤ qLine (ln₀' F) :=
  sup_le (xPoint_le_qLine isLine_ln₀' ((Submodule.span_singleton_le_iff_mem _ _).2 f₂_mem_ln₀'))
    (xPoint_le_qLine isLine_ln₀' ((Submodule.span_singleton_le_iff_mem _ _).2 f₁_mem_ln₀'))

omit [CharP F 2] in
theorem card_lt_xPoint_f₂_sup_f₁ :
    Nat.card F < Nat.card ↥(xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F)) := by
  have h := card_xPoint_sup (isPoint_span (f₂_ne_zero (F := F)))
    (isPoint_span (f₁_ne_zero (F := F)))
    span_f₁_ne_span_f₂.symm
    ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_perp_span.2 (by simp [form_apply])))
  have hq : 1 < Nat.card F := Finite.one_lt_card
  calc Nat.card F < Nat.card F ^ 2 := by
        calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
          _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
    _ ≤ _ := h

theorem sup_eq_top_std_of_card {J : Subgroup (Sp4 F)} (hJ : J ≤ Q₁ F)
    (hJc : Nat.card F ^ 2 < Nat.card J) :
    J ⊔ xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) = ⊤ := by
  have h := sup_eq_top_of_le_qLine' isLine_ln₀' isLine_ln₀
    (by rw [inf_comm]; exact ln₀_inf_ln₀') xPoint_f₂_sup_f₁_le hJ card_lt_xPoint_f₂_sup_f₁ hJc
  rw [sup_assoc, sup_comm]
  exact h

omit [Finite F] in
theorem qe_zero_mem_Q₁ (x s : F) : qe x 0 s ∈ Q₁ F := fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [qe_mulVec, h0, h1]
  simp

theorem sup_eq_top_std_of_le_Q₂ {J : Subgroup (Sp4 F)} (hJ : J ≤ Q₁ F) (hJ₂ : J ≤ Q₂ F)
    (hJc : Nat.card J = Nat.card F ^ 2) :
    J ⊔ xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) = ⊤ := by
  set H := J ⊔ xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) with hH
  have hJeq : J = Q₁ F ⊓ Q₂ F :=
    Subgroup.eq_of_le_of_card_ge (le_inf hJ hJ₂) (by rw [hJc, card_Q₁_inf_Q₂])
  have hq0 : ∀ x s : F, qe x 0 s ∈ H := fun x s =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (hJeq ▸ ⟨qe_zero_mem_Q₁ x s, qe_mem_Q₂ x 0 s⟩))
  have hf₂ : ∀ c : F, transv (f₂ F) c ∈ H := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (transv_mem_xPoint _ c))
  have hf₁ : transv (f₁ F) 1 ∈ H := Subgroup.mem_sup_right (transv_mem_xPoint _ 1)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h0y : ∀ y t : F, qe 0 y t ∈ H := by
    intro y t
    have h1 := mul_mem (mul_mem (mul_mem (hf₂ y) (hq0 1 0)) (inv_mem (hf₂ y))) (hq0 1 (t + y))
    rw [qe_conj_transv_f₂, qe_mul, qe_congr (x' := 0) (y' := y) (s' := t) (by linear_combination h2)
      (by ring) (by linear_combination y * h2)] at h1
    exact h1
  have hQ₂ : Q₂ F ≤ H := by
    intro g hg
    obtain ⟨x, y, s, rfl⟩ := exists_eq_qe_of_mem_Q₂ hg
    have h1 := mul_mem (hq0 x s) (h0y y (x * y))
    rw [qe_mul, qe_congr (x' := x) (y' := y) (s' := s) (by ring) (by ring)
      (by linear_combination (x * y) * h2)] at h1
    exact h1
  refine eq_top_iff.2 ((Q₂_sup_zpowers_transv one_ne_zero).symm.le.trans (sup_le hQ₂ ?_))
  rw [Subgroup.zpowers_le]
  exact hf₁

omit [Finite F] in
theorem sup_eq_top_std_of_transv {J : Subgroup (Sp4 F)} (hJ : J ≤ Q₁ F)
    (he₁ : ∀ s, transv (e₁ F) s ∈ J) {c₁ : F} (hc₁ : c₁ ≠ 0) (he₂ : transv (e₂ F) c₁ ∈ J)
    {g : Sp4 F} (hg : g ∈ J) (hgc : mat g (.inl 0) (.inr 1) ≠ 0) :
    J ⊔ xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) = ⊤ := by
  set H := J ⊔ xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) with hH
  have hJH : J ≤ H := le_sup_left.trans le_sup_left
  have h1 : ∀ s, transv (e₁ F) s ∈ H := fun s => hJH (he₁ s)
  have h4 : ∀ s, transv (f₂ F) s ∈ H := fun s =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (transv_mem_xPoint _ s))
  have h3 : ∀ s, transv (f₁ F) s ∈ H := fun s => Subgroup.mem_sup_right (transv_mem_xPoint _ s)
  have h2 : ∀ s, transv (e₂ F) s ∈ H :=
    transv_mem_of_weyl (a := f₂ F) (by rw [form_f₂]; simp [CharTwo.neg_eq]) h4 hc₁ (hJH he₂)
  set b₀ := mat g (.inl 0) (.inr 0)
  set c₀ := mat g (.inl 0) (.inr 1)
  have hgf : mat g *ᵥ f₁ F = f₁ F + b₀ • e₁ F + c₀ • e₂ F := by
    rw [mulVec_of_mem_Q₁ (hJ hg)]
    simp [b₀, c₀]
  have hg' : transv (e₁ F) b₀ * g ∈ H := mul_mem (h1 _) (hJH hg)
  have hg'f : mat (transv (e₁ F) b₀ * g) *ᵥ f₁ F = f₁ F + c₀ • e₂ F := by
    rw [mat_mul_mulVec, hgf, transv_mulVec, form_e₁]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
    grind
  have h5 : ∀ s, transv (f₁ F + c₀ • e₂ F) s ∈ H := fun s => by
    rw [← hg'f, ← transv_conj]
    exact mul_mem (mul_mem hg' (h3 s)) (inv_mem hg')
  have hh : transv (e₂ F) c₀ * transv (f₂ F) c₀⁻¹ ∈ H := mul_mem (h2 _) (h4 _)
  have hhf : mat (transv (e₂ F) c₀ * transv (f₂ F) c₀⁻¹) *ᵥ (f₁ F + c₀ • e₂ F) =
      f₁ F + f₂ F := by
    rw [mat_mul_mulVec, transv_mulVec, transv_mulVec, form_f₂, form_e₂]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [CharTwo.neg_eq, hgc]
    grind
  have h6 : ∀ s, transv (f₁ F + f₂ F) s ∈ H := fun s => by
    rw [← hhf, ← transv_conj]
    exact mul_mem (mul_mem hh (h5 s)) (inv_mem hh)
  have hj : jSwap F ∈ H := mul_mem (mul_mem (mul_mem (h1 1) (h3 1)) (h1 1))
    (mul_mem (mul_mem (h2 1) (h4 1)) (h2 1))
  have h7 : ∀ s, transv (e₁ F + e₂ F) s ∈ H := fun s => by
    have hjf : mat (jSwap F) *ᵥ (f₁ F + f₂ F) = e₁ F + e₂ F := by
      rw [jSwap_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
    rw [← hjf, ← transv_conj]
    exact mul_mem (mul_mem hj (h6 s)) (inv_mem hj)
  exact eq_top_of_five H h1 h2 h3 h4 h7

end Std

section XElem

variable [CharP F 2]

omit [CharP F 2] in
theorem e₁_add_e₂_ne_zero' : e₁ F + e₂ F ≠ 0 := fun h => by simpa using congrFun h (.inl 0)

omit [CharP F 2] in
theorem f₁_add_f₂_ne_zero : f₁ F + f₂ F ≠ 0 := fun h => by simpa using congrFun h (.inr 0)

omit [CharP F 2] in
theorem e₁_add_e₂_add_f₁_add_f₂_ne_zero : e₁ F + e₂ F + f₁ F + f₂ F ≠ 0 := fun h => by
  simpa using congrFun h (.inl 0)

omit [CharP F 2] in
theorem f₂_add_e₁_ne_zero : f₂ F + e₁ F ≠ 0 := fun h => by simpa using congrFun h (.inr 1)

@[expose] def xZero (F : Type) [Field F] : Sp4 F := xAlt F * wAl F

@[expose] def xOne (F : Type) [Field F] : Sp4 F := xAlt F * nuE 1

theorem xZero_mulVec (v : V4 F) :
    mat (xZero F) *ᵥ v = (v (.inl 1) + v (.inr 0)) • e₁ F + (v (.inl 0) + v (.inr 1)) • e₂ F +
      v (.inr 1) • f₁ F + v (.inr 0) • f₂ F := by
  rw [xZero, mat_mul_mulVec, wAl_mulVec, xAlt_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem xOne_mulVec (v : V4 F) :
    mat (xOne F) *ᵥ v = (v (.inl 0) + v (.inl 1) + v (.inr 0) + v (.inr 1)) • e₁ F +
      (v (.inl 1) + v (.inr 0)) • e₂ F + v (.inr 0) • f₁ F + (v (.inr 1) + v (.inr 0)) • f₂ F := by
  rw [xOne, mat_mul_mulVec, nuE_mulVec, xAlt_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp
  ring

variable [Finite F]

theorem xZero_mem_commutator : xZero F ∈ commutator (Sp4 F) := by
  have e : xZero F = (transv (e₁ F) 1 * transv (e₂ F) 1) *
      (transv (e₁ F + e₂ F) 1 * transv (e₁ F + e₂ F) 1) *
      (transv (f₁ F + f₂ F) 1 * transv (e₁ F + e₂ F + f₁ F + f₂ F) 1) := by
    rw [xZero, xAlt, wAl]
    group
  rw [e]
  have h := fun {u v : V4 F} (hu : u ≠ 0) (hv : v ≠ 0) =>
    transv_mul_transv_mem_commutator hu hv (one_ne_zero (α := F)) (one_ne_zero (α := F))
  exact mul_mem (mul_mem (h e₁_ne_zero e₂_ne_zero) (h e₁_add_e₂_ne_zero' e₁_add_e₂_ne_zero'))
    (h f₁_add_f₂_ne_zero e₁_add_e₂_add_f₁_add_f₂_ne_zero)

theorem xOne_mem_commutator : xOne F ∈ commutator (Sp4 F) := by
  have e : xOne F = (transv (e₁ F) 1 * transv (e₂ F) 1) *
      (transv (e₁ F + e₂ F) 1 * transv (f₂ F + e₁ F) 1) *
      (transv (f₂ F) 1 * transv (e₁ F) 1) := by
    rw [xOne, xAlt, nuE]
    group
  rw [e]
  have h := fun {u v : V4 F} (hu : u ≠ 0) (hv : v ≠ 0) =>
    transv_mul_transv_mem_commutator hu hv (one_ne_zero (α := F)) (one_ne_zero (α := F))
  exact mul_mem (mul_mem (h e₁_ne_zero e₂_ne_zero) (h e₁_add_e₂_ne_zero' f₂_add_e₁_ne_zero))
    (h f₂_ne_zero e₁_ne_zero)

omit [Finite F] in
theorem xZero_mem_stab : xZero F ∈ stab (ln₀ F) := mem_stab_of_le fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [mem_ln₀, xZero_mulVec]
  simp [h0, h1]

omit [Finite F] in
theorem xOne_mem_stab : xOne F ∈ stab (ln₀ F) := mem_stab_of_le fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [mem_ln₀, xOne_mulVec]
  simp [h0, h1]

omit [Finite F] [CharP F 2] in
theorem map_inv_inf_eq_bot {g : Sp4 F} {W : Submodule F (V4 F)}
    (h : ∀ v ∈ W, mat g *ᵥ v ∈ W → v = 0) : W.map (mulVecLin (mat g⁻¹)) ⊓ W = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  rw [mem_map_mulVecLin, inv_inv] at hv1
  exact (Submodule.mem_bot F).2 (h v hv2 hv1)

omit [Finite F] in
theorem xZero_opp : (ln₀' F).map (mulVecLin (mat (xZero F)⁻¹)) ⊓ ln₀' F = ⊥ := by
  refine map_inv_inf_eq_bot fun v hv hv' => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀'.1 hv
  obtain ⟨h2, h3⟩ := mem_ln₀'.1 hv'
  rw [xZero_mulVec] at h2 h3
  simp [h0, h1] at h2 h3
  exact ext4 (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h3])

omit [Finite F] in
theorem xOne_opp : (ln₀' F).map (mulVecLin (mat (xOne F)⁻¹)) ⊓ ln₀' F = ⊥ := by
  refine map_inv_inf_eq_bot fun v hv hv' => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀'.1 hv
  obtain ⟨h2, h3⟩ := mem_ln₀'.1 hv'
  rw [xOne_mulVec] at h2 h3
  simp [h0, h1] at h2 h3
  have h4 : v (.inr 1) = 0 := by rw [h3, zero_add] at h2; exact h2
  exact ext4 (by simp [h0]) (by simp [h1]) (by simp [h3]) (by simp [h4])

end XElem

section Transport

omit [Field F] in
theorem map_conj_map_conj' {Γ : Type*} [Group Γ] (K : Subgroup Γ) (a b : Γ) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom :=
  map_conj_map_conj K b a

omit [Field F] in
theorem eq_top_of_map_conj {Γ : Type*} [Group Γ] {K : Subgroup Γ} (c : Γ)
    (h : K.map (MulAut.conj c).toMonoidHom = ⊤) : K = ⊤ := by
  have hs : Function.Surjective (MulAut.conj c).toMonoidHom := (MulAut.conj c).surjective
  rw [← Subgroup.map_top_of_surjective _ hs] at h
  exact Subgroup.map_injective (MulAut.conj c).injective h

omit [Field F] in
theorem map_conj_one {Γ : Type*} [Group Γ] (K : Subgroup Γ) :
    K.map (MulAut.conj (1 : Γ)).toMonoidHom = K := by
  ext x
  simp

theorem map_span_eq (g : Sp4 F) (v : V4 F) :
    (F ∙ v).map (mulVecLin (mat g)) = F ∙ (mat g *ᵥ v) := by
  rw [Submodule.map_span, Set.image_singleton]
  rfl

variable [CharP F 2]

theorem sig_map_ln₀ : (ln₀ F).map (mulVecLin (mat (sig F))) = ln₀' F := by
  ext v
  rw [mem_map_mulVecLin, sig_inv, mem_ln₀, mem_ln₀', sig_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp
  tauto

theorem sig_map_pt₀ : (pt₀ F).map (mulVecLin (mat (sig F))) = F ∙ f₂ F := by
  rw [pt₀_eq_span, map_span_eq, sig_mulVec]
  congr 2
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem sig_map_e₂ : (F ∙ e₂ F).map (mulVecLin (mat (sig F))) = F ∙ f₁ F := by
  rw [map_span_eq, sig_mulVec]
  congr 2
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem transport_lines {l : Submodule F (V4 F)} {φ : Sp4 F}
    (hφl : (ln₀ F).map (mulVecLin (mat φ)) = l) {x₀ : Sp4 F} (hx₀s : x₀ ∈ stab (ln₀ F))
    (hx₀l : (ln₀' F).map (mulVecLin (mat x₀⁻¹)) ⊓ ln₀' F = ⊥) :
    φ * x₀ * φ⁻¹ ∈ stab l ∧
      l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹))).map (mulVecLin (mat (φ * x₀ * φ⁻¹)⁻¹)) ⊓
        l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) = ⊥ := by
  have hg : (φ * sig F * φ⁻¹)⁻¹ = φ * sig F * φ⁻¹ := by
    rw [show (φ * sig F * φ⁻¹)⁻¹ = φ * (sig F)⁻¹ * φ⁻¹ by group, sig_inv]
  have hl₁ : l.map (mulVecLin (mat (φ * sig F * φ⁻¹)⁻¹)) = (ln₀' F).map (mulVecLin (mat φ)) := by
    rw [hg, ← hφl, map_mat_mul, map_mat_mul, map_map_mat_inv', sig_map_ln₀]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_stab_iff, ← hφl, map_mat_mul, map_mat_mul, map_map_mat_inv', mem_stab_iff.1 hx₀s]
  · rw [hl₁, ← hφl, ← map_inf_map, inf_comm, ln₀_inf_ln₀', Submodule.map_bot]
  · rw [hl₁, show (φ * x₀ * φ⁻¹)⁻¹ = φ * x₀⁻¹ * φ⁻¹ by group, map_mat_mul, map_mat_mul,
      map_map_mat_inv', ← map_inf_map, hx₀l, Submodule.map_bot]

theorem transport_conj (K : Subgroup (Sp4 F)) (φ x₀ : Sp4 F) :
    (K.map (MulAut.conj (φ * sig F * φ⁻¹)⁻¹).toMonoidHom).map
        (MulAut.conj (sig F * φ⁻¹)).toMonoidHom = K.map (MulAut.conj φ⁻¹).toMonoidHom ∧
      (K.map (MulAut.conj (φ * x₀ * φ⁻¹)).toMonoidHom).map
        (MulAut.conj (sig F * φ⁻¹)).toMonoidHom =
        ((K.map (MulAut.conj φ⁻¹).toMonoidHom).map (MulAut.conj x₀).toMonoidHom).map
          (MulAut.conj (sig F)).toMonoidHom ∧
      K.map (MulAut.conj (sig F * φ⁻¹)).toMonoidHom =
        (K.map (MulAut.conj φ⁻¹).toMonoidHom).map (MulAut.conj (sig F)).toMonoidHom := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_conj_map_conj']
    congr 3
    group
  · rw [map_conj_map_conj', map_conj_map_conj', map_conj_map_conj']
    congr 3
    group
  · rw [map_conj_map_conj']

end Transport

section CaseP

variable [CharP F 2]

theorem nuE_mulVec_e₁ (a : F) : mat (nuE a) *ᵥ e₁ F = e₁ F := by
  rw [nuE_mulVec]
  simp

theorem nuE_mulVec_e₂ (a : F) : mat (nuE a) *ᵥ e₂ F = a • e₁ F + e₂ F := by
  rw [nuE_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem nuE_mem_stab (a : F) : nuE a ∈ stab (ln₀ F) := mem_stab_of_le fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [mem_ln₀, nuE_mulVec]
  simp [h0, h1]

theorem xZero_map_pt₀ : (pt₀ F).map (mulVecLin (mat (xZero F))) = F ∙ e₂ F := by
  rw [pt₀_eq_span, map_span_eq, xZero_mulVec]
  congr 2
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem mem_Q₂_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) (hd : mat g (.inl 1) (.inr 1) = 0) :
    g ∈ Q₂ F := by
  have e : g = qe (mat g (.inl 0) (.inr 1)) 0 (mat g (.inl 0) (.inr 0)) := by
    refine ext_mulVec fun v => ?_
    rw [mulVec_of_mem_Q₁ hg, qe_mulVec, hd]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  rw [e]
  exact qe_mem_Q₂ _ _ _

omit [CharP F 2] in
theorem mul_transv_eq_transv {g : Sp4 F} (hg : g ∈ Q₁ F) (hd : mat g (.inl 1) (.inr 1) ≠ 0) :
    g * transv (e₁ F) (mat g (.inl 1) (.inr 1) *
        (mat g (.inl 0) (.inr 1) / mat g (.inl 1) (.inr 1)) ^ 2 - mat g (.inl 0) (.inr 0)) =
      transv ((mat g (.inl 0) (.inr 1) / mat g (.inl 1) (.inr 1)) • e₁ F + e₂ F)
        (mat g (.inl 1) (.inr 1)) := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, mulVec_of_mem_Q₁ hg, transv_mulVec, transv_mulVec, form_e₁]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, form_e₁, form_e₂,
    smul_eq_mul]
  generalize mat g (.inl 0) (.inr 0) = b at hd ⊢
  generalize mat g (.inl 0) (.inr 1) = c at hd ⊢
  generalize mat g (.inl 1) (.inr 1) = d at hd ⊢
  refine ext4 ?_ ?_ ?_ ?_ <;> simp
  all_goals field_simp
  ring

variable [Finite F]

omit [CharP F 2] in
theorem transv_e₂_mem_of_card {J : Subgroup (Sp4 F)} (hJ : J ≤ Q₁ F)
    (hJc : Nat.card J = Nat.card F ^ 2) (h0 : ∀ g ∈ J, mat g (.inl 0) (.inr 1) = 0) (s : F) :
    transv (e₂ F) s ∈ J := by
  let f : J → F × F := fun g =>
    (mat (g : Sp4 F) (.inl 0) (.inr 0), mat (g : Sp4 F) (.inl 1) (.inr 1))
  have hf : Function.Injective f := fun g g' hgg => Subtype.ext (eq_of_mem_Q₁ (hJ g.2) (hJ g'.2)
    (congrArg Prod.fst hgg) (by rw [h0 _ g.2, h0 _ g'.2]) (congrArg Prod.snd hgg))
  have hb := hf.bijective_of_nat_card_le (by rw [Nat.card_prod, hJc, sq])
  obtain ⟨g, hg⟩ := hb.2 (0, s)
  have e : (g : Sp4 F) = transv (e₂ F) s := by
    refine eq_of_mem_Q₁ (hJ g.2) (transv_e₂_mem_Q₁ s) ?_ ?_ ?_
    · rw [entry_transv_e₂]
      exact congrArg Prod.fst hg
    · rw [entry_transv_e₂, h0 _ g.2]
      simp
    · rw [entry_transv_e₂]
      exact congrArg Prod.snd hg
  rw [← e]
  exact g.2

theorem exists_caseP {l p : Submodule F (V4 F)} (hl : IsLine l) (hp : IsPoint p) (hpl : p ≤ l)
    {J : Subgroup (Sp4 F)} (hJl : J ≤ qLine l) (hJc : Nat.card F ^ 2 ≤ Nat.card J)
    (hJ2 : Nat.card J = Nat.card F ^ 2 → xPoint p ≤ J ∧
      ∀ p', IsPoint p' → p' ≤ l → p' ≠ p → ¬ xPoint p ⊔ xPoint p' ≤ J) :
    ∃ g x : Sp4 F, x ∈ commutator (Sp4 F) ∧ x ∈ stab l ∧
      l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
        l.map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      J.map (MulAut.conj g⁻¹).toMonoidHom ⊔ xPoint p ⊔
        xPoint (p.map (mulVecLin (mat x))) = ⊤ := by
  suffices key : ∃ φ : Sp4 F, (pt₀ F).map (mulVecLin (mat φ)) = p ∧
      (ln₀ F).map (mulVecLin (mat φ)) = l ∧
      J.map (MulAut.conj φ⁻¹).toMonoidHom ⊔ xPoint (F ∙ f₂ F) ⊔ xPoint (F ∙ f₁ F) = ⊤ by
    obtain ⟨φ, hφp, hφl, htop⟩ := key
    obtain ⟨hxs, hopp, hopp'⟩ := transport_lines hφl xZero_mem_stab xZero_opp
    refine ⟨φ * sig F * φ⁻¹, φ * xZero F * φ⁻¹,
      (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ xZero_mem_commutator φ, hxs, hopp,
      hopp', ?_⟩
    obtain ⟨h1, h2, h3⟩ := transport_conj (xPoint p) φ (xZero F)
    refine eq_top_of_map_conj (sig F * φ⁻¹) ?_
    rw [Subgroup.map_sup, Subgroup.map_sup, (transport_conj J φ (xZero F)).1, h3,
      ← xPoint_map_conj, h2, xPoint_map_conj, xPoint_map_conj, ← hφp, map_map_mat_inv',
      xPoint_map_conj, xZero_map_pt₀, xPoint_map_conj, sig_map_pt₀, sig_map_e₂]
    exact htop
  obtain ⟨φ₀, hφ₀p, hφ₀l⟩ := exists_map_flag hp hl hpl
  have hJ₀Q : J.map (MulAut.conj φ₀⁻¹).toMonoidHom ≤ Q₁ F :=
    (Subgroup.map_mono hJl).trans (qLine_map_conj_inv φ₀ hφ₀l).le
  have hJ₀c : Nat.card ↥(J.map (MulAut.conj φ₀⁻¹).toMonoidHom) = Nat.card J :=
    Subgroup.card_map_of_injective (MulAut.conj φ₀⁻¹).injective
  rcases hJc.lt_or_eq with hlt | heq
  · exact ⟨φ₀, hφ₀p, hφ₀l, sup_eq_top_std_of_card hJ₀Q (hJ₀c ▸ hlt)⟩
  obtain ⟨hXp, h51⟩ := hJ2 heq.symm
  have hX₂ : X₂ F ≤ J.map (MulAut.conj φ₀⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj φ₀⁻¹).toMonoidHom) hXp
    rwa [xPoint_map_conj, ← hφ₀p, map_map_mat_inv'] at this
  by_cases hQ₂ : J.map (MulAut.conj φ₀⁻¹).toMonoidHom ≤ Q₂ F
  · exact ⟨φ₀, hφ₀p, hφ₀l, sup_eq_top_std_of_le_Q₂ hJ₀Q hQ₂ (hJ₀c.trans heq.symm)⟩
  obtain ⟨g, hgJ, hgQ⟩ := Set.not_subset.1 hQ₂
  have hd : mat g (.inl 1) (.inr 1) ≠ 0 := fun hd => hgQ (mem_Q₂_of_mem_Q₁ (hJ₀Q hgJ) hd)
  set lam := mat g (.inl 0) (.inr 1) / mat g (.inl 1) (.inr 1) with hlam
  set d := mat g (.inl 1) (.inr 1) with hdd
  have ht : transv (lam • e₁ F + e₂ F) d ∈ J.map (MulAut.conj φ₀⁻¹).toMonoidHom := by
    rw [hlam, hdd, ← mul_transv_eq_transv (hJ₀Q hgJ) hd]
    exact mul_mem hgJ (hX₂ (transv_mem_X₂ _))
  set ν := nuE lam with hν
  have hνe₁ : mat ν⁻¹ *ᵥ e₁ F = e₁ F := by
    rw [← nuE_mulVec_e₁ lam, mat_inv_mulVec, ← hν, nuE_mulVec_e₁]
  have hνe₂ : mat ν⁻¹ *ᵥ (lam • e₁ F + e₂ F) = e₂ F := by
    rw [← nuE_mulVec_e₂ lam, ← hν, mat_inv_mulVec]
  set J₀ := J.map (MulAut.conj (φ₀ * ν)⁻¹).toMonoidHom with hJ₀
  have hJ₀' : J₀ = (J.map (MulAut.conj φ₀⁻¹).toMonoidHom).map (MulAut.conj ν⁻¹).toMonoidHom := by
    rw [hJ₀, map_conj_map_conj', _root_.mul_inv_rev]
  have hmem : ∀ y ∈ J.map (MulAut.conj φ₀⁻¹).toMonoidHom, ν⁻¹ * y * ν⁻¹⁻¹ ∈ J₀ := fun y hy => by
    rw [hJ₀']
    exact ⟨y, hy, rfl⟩
  have hφp : (pt₀ F).map (mulVecLin (mat (φ₀ * ν))) = p := by
    rw [map_mat_mul, pt₀_eq_span, map_span_eq, hν, nuE_mulVec_e₁, ← pt₀_eq_span, hφ₀p]
  have hφl : (ln₀ F).map (mulVecLin (mat (φ₀ * ν))) = l := by
    rw [map_mat_mul, mem_stab_iff.1 (nuE_mem_stab lam), hφ₀l]
  refine ⟨φ₀ * ν, hφp, hφl, ?_⟩
  have hJ₀Q' : J₀ ≤ Q₁ F := by
    rw [hJ₀']
    refine (Subgroup.map_mono hJ₀Q).trans (le_of_eq ?_)
    exact (mem_normalizer_iff_map_conj.1 (stab_le_normalizer_fixer _
      (inv_mem (nuE_mem_stab lam))))
  have he₁ : ∀ s, transv (e₁ F) s ∈ J₀ := fun s => by
    have := hmem _ (hX₂ (transv_mem_X₂ s))
    rwa [transv_conj, hνe₁] at this
  have he₂ : transv (e₂ F) d ∈ J₀ := by
    have := hmem _ ht
    rwa [transv_conj, hνe₂] at this
  have hJ₀c' : Nat.card J₀ = Nat.card F ^ 2 :=
    (Subgroup.card_map_of_injective (MulAut.conj _).injective).trans heq.symm
  have hnot : ¬ ∀ s, transv (e₂ F) s ∈ J₀ := by
    intro hall
    have hX : xPoint (F ∙ e₂ F) ≤ J₀ := fun y hy => by
      obtain ⟨c, rfl⟩ := (mem_xPoint_span e₂_ne_zero).1 hy
      exact hall c
    have hX' := Subgroup.map_mono (f := (MulAut.conj (φ₀ * ν)).toMonoidHom) hX
    rw [xPoint_map_conj, hJ₀, map_conj_map_conj', mul_inv_cancel, map_conj_one] at hX'
    refine h51 _ ?_ ?_ ?_ (sup_le hXp hX')
    · rw [map_span_eq]
      exact isPoint_span fun h => e₂_ne_zero (mulVec_mat_injective _ (h.trans (mulVec_zero _).symm))
    · rw [← hφl]
      exact Submodule.map_mono ((Submodule.span_singleton_le_iff_mem _ _).2
        (mem_ln₀.2 ⟨by simp, by simp⟩))
    · intro h
      rw [← hφp, pt₀_eq_span] at h
      have h' := congrArg (Submodule.map (mulVecLin (mat (φ₀ * ν)⁻¹))) h
      rw [map_map_mat_inv', map_map_mat_inv'] at h'
      have : e₂ F ∈ F ∙ e₁ F := h' ▸ Submodule.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
      have := congrFun hc (.inl 1)
      simp at this
  have hc : ∃ g' ∈ J₀, mat g' (.inl 0) (.inr 1) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hnot (transv_e₂_mem_of_card hJ₀Q' hJ₀c' hall)
  obtain ⟨g', hg'J, hg'c⟩ := hc
  exact sup_eq_top_std_of_transv hJ₀Q' he₁ hd he₂ hg'J hg'c

end CaseP

section CaseHat

variable [CharP F 2]

omit [CharP F 2] in
theorem conj_transv_mul_transv (g : Sp4 F) (u v : V4 F) (c d : F) :
    g * (transv u c * transv v d) * g⁻¹ = transv (mat g *ᵥ u) c * transv (mat g *ᵥ v) d := by
  rw [← transv_conj, ← transv_conj]
  group

omit [CharP F 2] in
theorem eq_zero_or_eq_one_of_card_two (hq : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hq
  exact eq_zero_or_eq_one_of_ringEquiv c a

theorem exists_frame_two (hq : Nat.card F = 2) {l : Submodule F (V4 F)} (hl : IsLine l)
    {v₁ v₂ : V4 F} (h₁ : v₁ ≠ 0) (h₁₂ : v₁ ≠ v₂) (hv₁ : v₁ ∈ l) (hv₂ : v₂ ∈ l) (h₂ : v₂ ≠ 0) :
    ∃ φ : Sp4 F, mat φ *ᵥ e₁ F = v₁ ∧ mat φ *ᵥ e₂ F = v₂ ∧
      (ln₀ F).map (mulVecLin (mat φ)) = l := by
  have h01 := eq_zero_or_eq_one_of_card_two hq
  obtain ⟨φ₀, hφ₀p, hφ₀l⟩ := exists_map_flag (isPoint_span h₁) hl
    ((Submodule.span_singleton_le_iff_mem _ _).2 hv₁)
  have hw₁ : mat φ₀⁻¹ *ᵥ v₁ ∈ pt₀ F :=
    mem_map_mulVecLin.1 (hφ₀p ▸ Submodule.mem_span_singleton_self v₁)
  have hw₂ : mat φ₀⁻¹ *ᵥ v₂ ∈ ln₀ F := mem_map_mulVecLin.1 (hφ₀l ▸ hv₂)
  obtain ⟨a1, a2, a3⟩ := mem_pt₀.1 hw₁
  obtain ⟨b2, b3⟩ := mem_ln₀.1 hw₂
  have hne : ∀ v : V4 F, v ≠ 0 → mat φ₀⁻¹ *ᵥ v ≠ 0 := fun v hv h =>
    hv (by rw [← mat_mulVec_inv φ₀ v, h, mulVec_zero])
  have he₁ : mat φ₀⁻¹ *ᵥ v₁ = e₁ F := by
    rcases h01 ((mat φ₀⁻¹ *ᵥ v₁) (.inl 0)) with h | h
    · exact absurd (ext4 (by simp [h]) (by simp [a1]) (by simp [a2]) (by simp [a3]))
        (hne _ h₁)
    · exact ext4 (by simp [h]) (by simp [a1]) (by simp [a2]) (by simp [a3])
  set α := (mat φ₀⁻¹ *ᵥ v₂) (.inl 0)
  have he₂ : mat φ₀⁻¹ *ᵥ v₂ = α • e₁ F + e₂ F := by
    rcases h01 ((mat φ₀⁻¹ *ᵥ v₂) (.inl 1)) with h | h
    · exfalso
      rcases h01 α with hα | hα
      · exact hne _ h₂ (ext4 (by simp [hα, α]) (by simp [h]) (by simp [b2]) (by simp [b3]))
      · refine h₁₂ ?_
        rw [← mat_mulVec_inv φ₀ v₁, ← mat_mulVec_inv φ₀ v₂, he₁]
        congr 1
        exact (ext4 (by simp [hα, α]) (by simp [h]) (by simp [b2]) (by simp [b3])).symm
    · exact ext4 (by simp [α]) (by simp [h]) (by simp [b2]) (by simp [b3])
  refine ⟨φ₀ * nuE α, ?_, ?_, ?_⟩
  · rw [mat_mul_mulVec, nuE_mulVec_e₁, ← he₁, mat_mulVec_inv]
  · rw [mat_mul_mulVec, nuE_mulVec_e₂, ← he₂, mat_mulVec_inv]
  · rw [map_mat_mul, mem_stab_iff.1 (nuE_mem_stab α), hφ₀l]

theorem sig_mulVec_e₁ : mat (sig F) *ᵥ e₁ F = f₂ F := by
  rw [sig_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem sig_mulVec_e₂ : mat (sig F) *ᵥ e₂ F = f₁ F := by
  rw [sig_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem xOne_mulVec_e₁ : mat (xOne F) *ᵥ e₁ F = e₁ F := by
  rw [xOne_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem xOne_mulVec_e₂ : mat (xOne F) *ᵥ e₂ F = e₁ F + e₂ F := by
  rw [xOne_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

variable [Finite F]

theorem card_closure_pair_gt :
    2 < Nat.card ↥(Subgroup.closure {transv (f₂ F) 1 * transv (f₁ F) 1,
      transv (f₂ F) 1 * transv (mat (sig F) *ᵥ (e₁ F + e₂ F)) 1}) := by
  set a := transv (f₂ F) 1 * transv (f₁ F) 1
  set b := transv (f₂ F) 1 * transv (mat (sig F) *ᵥ (e₁ F + e₂ F)) 1
  have hae : mat a *ᵥ e₁ F = e₁ F + f₁ F := by
    simp only [a, mat_mul_mulVec, transv_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq]
  have hbe : mat b *ᵥ e₁ F = e₁ F + f₁ F + f₂ F := by
    simp only [b, mat_mul_mulVec, transv_mulVec, sig_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, CharTwo.neg_eq]
  have ha1 : a ≠ 1 := fun h => by
    have := congrFun (hae.symm.trans (by rw [h, mat_one, one_mulVec])) (.inr 0)
    simp at this
  have hb1 : b ≠ 1 := fun h => by
    have := congrFun (hbe.symm.trans (by rw [h, mat_one, one_mulVec])) (.inr 0)
    simp at this
  have hab : a ≠ b := fun h => by
    have := congrFun (hae.symm.trans (by rw [h, hbe])) (.inr 1)
    simp at this
  let E := Subgroup.closure ({a, b} : Set (Sp4 F))
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  let f : Fin 3 → E := ![1, ⟨a, haE⟩, ⟨b, hbE⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢ <;>
      first | exact absurd hij' ha1 | exact absurd hij'.symm ha1 | exact absurd hij' hb1 |
        exact absurd hij'.symm hb1 | exact absurd hij' hab | exact absurd hij'.symm hab
  have := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  exact this

theorem exists_caseHat (hq : Nat.card F = 2) {l : Submodule F (V4 F)} (hl : IsLine l)
    {v₁ v₂ : V4 F} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (h₁₂ : v₁ ≠ v₂) (hv₁ : v₁ ∈ l) (hv₂ : v₂ ∈ l)
    {J : Subgroup (Sp4 F)} (hJl : J ≤ qLine l) (hJc : Nat.card F ^ 2 < Nat.card J)
    {Z : Subgroup (Sp4 F)} (hZ : transv v₁ 1 * transv v₂ 1 ∈ Z) :
    ∃ g x : Sp4 F, x ∈ commutator (Sp4 F) ∧ x ∈ stab l ∧
      l.map (mulVecLin (mat g⁻¹)) ⊓ l = ⊥ ∧
      (l.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat x⁻¹)) ⊓
        l.map (mulVecLin (mat g⁻¹)) = ⊥ ∧
      J.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z ⊔ Z.map (MulAut.conj x).toMonoidHom = ⊤ := by
  obtain ⟨φ, hφ₁, hφ₂, hφl⟩ := exists_frame_two hq hl h₁ h₁₂ hv₁ hv₂ h₂
  obtain ⟨hxs, hopp, hopp'⟩ := transport_lines hφl xOne_mem_stab xOne_opp
  refine ⟨φ * sig F * φ⁻¹, φ * xOne F * φ⁻¹,
    (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ xOne_mem_commutator φ, hxs, hopp,
    hopp', ?_⟩
  obtain ⟨-, h2, h3⟩ := transport_conj Z φ (xOne F)
  refine eq_top_of_map_conj (sig F * φ⁻¹) ?_
  rw [Subgroup.map_sup, Subgroup.map_sup, (transport_conj J φ (xOne F)).1, h3, h2]
  set Z₀ := Z.map (MulAut.conj φ⁻¹).toMonoidHom
  have hs₀ : transv (e₁ F) 1 * transv (e₂ F) 1 ∈ Z₀ := by
    refine ⟨_, hZ, ?_⟩
    change φ⁻¹ * (transv v₁ 1 * transv v₂ 1) * φ⁻¹⁻¹ = _
    rw [conj_transv_mul_transv, ← hφ₁, ← hφ₂, mat_inv_mulVec, mat_inv_mulVec]
  have ha : transv (f₂ F) 1 * transv (f₁ F) 1 ∈ Z₀.map (MulAut.conj (sig F)).toMonoidHom := by
    refine ⟨_, hs₀, ?_⟩
    change sig F * (transv (e₁ F) 1 * transv (e₂ F) 1) * (sig F)⁻¹ = _
    rw [conj_transv_mul_transv, sig_mulVec_e₁, sig_mulVec_e₂]
  have hb : transv (f₂ F) 1 * transv (mat (sig F) *ᵥ (e₁ F + e₂ F)) 1 ∈
      (Z₀.map (MulAut.conj (xOne F)).toMonoidHom).map (MulAut.conj (sig F)).toMonoidHom := by
    refine ⟨_, ⟨_, hs₀, rfl⟩, ?_⟩
    change sig F * (xOne F * (transv (e₁ F) 1 * transv (e₂ F) 1) * (xOne F)⁻¹) * (sig F)⁻¹ = _
    rw [conj_transv_mul_transv, conj_transv_mul_transv, xOne_mulVec_e₁, xOne_mulVec_e₂,
      sig_mulVec_e₁]
  have hJ₀Q : J.map (MulAut.conj φ⁻¹).toMonoidHom ≤ Q₁ F :=
    (Subgroup.map_mono hJl).trans (qLine_map_conj_inv φ hφl).le
  have hJ₀c : Nat.card F ^ 2 < Nat.card ↥(J.map (MulAut.conj φ⁻¹).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj φ⁻¹).injective]
  have hσ : mat (sig F) *ᵥ (e₁ F + e₂ F) ∈ ln₀' F := by
    rw [mulVec_add, sig_mulVec_e₁, sig_mulVec_e₂]
    exact add_mem f₂_mem_ln₀' f₁_mem_ln₀'
  have hEl : Subgroup.closure {transv (f₂ F) 1 * transv (f₁ F) 1,
      transv (f₂ F) 1 * transv (mat (sig F) *ᵥ (e₁ F + e₂ F)) 1} ≤ qLine (ln₀' F) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact mul_mem (transv_mem_qLine isLine_ln₀' f₂_mem_ln₀' 1)
        (transv_mem_qLine isLine_ln₀' f₁_mem_ln₀' 1)
    · exact mul_mem (transv_mem_qLine isLine_ln₀' f₂_mem_ln₀' 1)
        (transv_mem_qLine isLine_ln₀' hσ 1)
  have htop := sup_eq_top_of_le_qLine' isLine_ln₀' isLine_ln₀
    (by rw [inf_comm]; exact ln₀_inf_ln₀') hEl hJ₀Q (by rw [hq]; exact card_closure_pair_gt)
    hJ₀c
  refine eq_top_iff.2 (htop.symm.le.trans (sup_le ?_ (le_sup_left.trans le_sup_left)))
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ha)
  · exact Subgroup.mem_sup_right hb

end CaseHat

section CaseLGeo

theorem perp_commSp (A : Subgroup (Sp4 F)) : perp (commSp A) = fixSp A := by
  ext w
  rw [mem_fixSp]
  constructor
  · intro hw a ha
    have h0 : ∀ v : V4 F, form F v (mat a *ᵥ w - w) = 0 := fun v => by
      have := mem_perp.1 hw _ (sub_mem_commSp (inv_mem ha) v)
      rw [map_sub, LinearMap.sub_apply, ← form_mat a (mat a⁻¹ *ᵥ v) w, mat_mulVec_inv] at this
      rw [map_sub, this]
    have h1 := form_nondegenerate.1 (mat a *ᵥ w - w) fun v => by
      rw [form_swap, h0 v, neg_zero]
    exact sub_eq_zero.1 h1
  · intro hw
    refine mem_perp.2 fun c hc => ?_
    have hle : commSp A ≤ perp (F ∙ w) := commSp_le_iff.2 fun a ha v => by
      have e : form F w (mat a *ᵥ v) = form F w v := by
        calc form F w (mat a *ᵥ v) = form F (mat a *ᵥ w) (mat a *ᵥ v) := by rw [hw a ha]
          _ = form F w v := form_mat a w v
      rw [mem_perp_span, map_sub, e, sub_self]
    rw [form_swap, mem_perp_span.1 (hle hc), neg_zero]

theorem two_le_finrank_fixSp {A : Subgroup (Sp4 F)} (h : commSp A ≤ fixSp A) :
    2 ≤ Module.finrank F (fixSp A) := by
  have h1 := finrank_perp (commSp A)
  rw [perp_commSp] at h1
  have h2 := Submodule.finrank_mono h
  omega

theorem qLine_inf_stab_eq_bot {m l : Submodule F (V4 F)} (hm : IsLine m) (hl : IsLine l)
    (hml : m ⊓ l = ⊥) : qLine m ⊓ stab l = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgm, hgl⟩ := Subgroup.mem_inf.1 hg
  have hfix : ∀ v ∈ l, mat g *ᵥ v = v := fun v hv => by
    have h1 : mat g *ᵥ v - v ∈ m := by
      have := sub_mem_perp_of_mem_fixer hgm v
      rwa [hm.perp_eq] at this
    have h2 : mat g *ᵥ v - v ∈ l := l.sub_mem (mulVec_mem_of_mem_stab hgl hv) hv
    have h3 : mat g *ᵥ v - v ∈ m ⊓ l := ⟨h1, h2⟩
    rw [hml, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  have htop : m ⊔ l = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have := Submodule.finrank_sup_add_finrank_inf_eq m l
    rw [hml, finrank_bot, hm.1, hl.1] at this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine (Subgroup.mem_bot).2 (ext_mulVec fun v => ?_)
  have hv : v ∈ m ⊔ l := htop ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  rw [mat_one, one_mulVec, mulVec_add, hgm y hy, hfix z hz]

theorem qLine_inf_stab_le_qPoint {m l p : Submodule F (V4 F)} (hm : IsLine m) (hl : IsLine l)
    (hp : IsPoint p) (hml : m ⊓ l = p) : qLine m ⊓ stab l ≤ qPoint p := by
  intro g hg
  obtain ⟨hgm, hgl⟩ := Subgroup.mem_inf.1 hg
  refine ⟨fun v hv => hgm v (by rw [← hml] at hv; exact hv.1), fun v hv => ?_⟩
  rw [← sup_eq_perp hm hl hp hml] at hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  have e : mat g *ᵥ (y + z) - (y + z) = mat g *ᵥ z - z := by
    rw [mulVec_add, hgm y hy]
    abel
  rw [e, ← hml]
  refine ⟨?_, l.sub_mem (mulVec_mem_of_mem_stab hgl hz) hz⟩
  have := sub_mem_perp_of_mem_fixer hgm z
  rwa [hm.perp_eq] at this

end CaseLGeo

section Levi

variable [CharP F 2]

@[expose] def q1c (g : Sp4 F) : F × F × F :=
  (mat g (.inl 0) (.inr 0), mat g (.inl 0) (.inr 1), mat g (.inl 1) (.inr 1))

omit [CharP F 2] in
theorem q1c_mul {g h : Sp4 F} (hg : g ∈ Q₁ F) (hh : h ∈ Q₁ F) : q1c (g * h) = q1c g + q1c h := by
  simp only [q1c, entry_mul_of_mem_Q₁ hg hh, Prod.mk_add_mk]

omit [CharP F 2] in
theorem q1c_inv {g : Sp4 F} (hg : g ∈ Q₁ F) : q1c g⁻¹ = -q1c g := by
  simp only [q1c, entry_inv_of_mem_Q₁ hg, Prod.neg_mk]

omit [CharP F 2] in
theorem q1c_inj {g h : Sp4 F} (hg : g ∈ Q₁ F) (hh : h ∈ Q₁ F) (e : q1c g = q1c h) : g = h :=
  eq_of_mem_Q₁ hg hh (congrArg Prod.fst e) (congrArg (fun x => x.2.1) e)
    (congrArg (fun x => x.2.2) e)

theorem nuE_mul_self (a : F) : nuE a * nuE a = 1 := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, nuE_mulVec, nuE_mulVec, mat_one, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp
  all_goals ring_nf
  all_goals simp [CharTwo.two_eq_zero]

theorem nuE_inv (a : F) : (nuE a)⁻¹ = nuE a := inv_eq_of_mul_eq_one_right (nuE_mul_self a)

theorem wAl_mul_self : wAl F * wAl F = 1 := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, wAl_mulVec, wAl_mulVec, mat_one, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem wAl_inv : (wAl F)⁻¹ = wAl F := inv_eq_of_mul_eq_one_right wAl_mul_self

theorem wAl_mem_stab : wAl F ∈ stab (ln₀ F) := mem_stab_of_le fun v hv => by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  rw [mem_ln₀, wAl_mulVec]
  simp [h0, h1]

omit [CharP F 2] in
theorem conj_mem_Q₁ {k : Sp4 F} (hk : k ∈ stab (ln₀ F)) {g : Sp4 F} (hg : g ∈ Q₁ F) :
    k * g * k⁻¹ ∈ Q₁ F :=
  (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_fixer _ hk) g).1 hg

theorem nuE_conj_mulVec {g : Sp4 F} (hg : g ∈ Q₁ F) (a : F) (v : V4 F) :
    mat (nuE a * g * (nuE a)⁻¹) *ᵥ v = v +
      ((mat g (.inl 0) (.inr 0) + a ^ 2 * mat g (.inl 1) (.inr 1)) * v (.inr 0) +
        (mat g (.inl 0) (.inr 1) + a * mat g (.inl 1) (.inr 1)) * v (.inr 1)) • e₁ F +
      ((mat g (.inl 0) (.inr 1) + a * mat g (.inl 1) (.inr 1)) * v (.inr 0) +
        mat g (.inl 1) (.inr 1) * v (.inr 1)) • e₂ F := by
  rw [nuE_inv, mat_mul_mulVec, mat_mul_mulVec, mulVec_of_mem_Q₁ hg (mat (nuE a) *ᵥ v),
    nuE_mulVec a v]
  rw [nuE_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> grind

theorem wAl_conj_mulVec {g : Sp4 F} (hg : g ∈ Q₁ F) (v : V4 F) :
    mat (wAl F * g * (wAl F)⁻¹) *ᵥ v = v +
      (mat g (.inl 1) (.inr 1) * v (.inr 0) + mat g (.inl 0) (.inr 1) * v (.inr 1)) • e₁ F +
      (mat g (.inl 0) (.inr 1) * v (.inr 0) + mat g (.inl 0) (.inr 0) * v (.inr 1)) • e₂ F := by
  rw [wAl_inv, mat_mul_mulVec, mat_mul_mulVec, mulVec_of_mem_Q₁ hg (mat (wAl F) *ᵥ v),
    wAl_mulVec v]
  rw [wAl_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> grind

omit [CharP F 2] in
theorem q1c_of_mulVec {g : Sp4 F} {b c d : F}
    (h : ∀ v, mat g *ᵥ v = v + (b * v (.inr 0) + c * v (.inr 1)) • e₁ F +
      (c * v (.inr 0) + d * v (.inr 1)) • e₂ F) : q1c g = (b, c, d) := by
  simp only [q1c, mat_apply_eq, h]
  simp

theorem q1c_nuE_conj {g : Sp4 F} (hg : g ∈ Q₁ F) (a : F) :
    q1c (nuE a * g * (nuE a)⁻¹) =
      ((q1c g).1 + a ^ 2 * (q1c g).2.2, (q1c g).2.1 + a * (q1c g).2.2, (q1c g).2.2) :=
  q1c_of_mulVec (nuE_conj_mulVec hg a)

theorem q1c_wAl_conj {g : Sp4 F} (hg : g ∈ Q₁ F) :
    q1c (wAl F * g * (wAl F)⁻¹) = ((q1c g).2.2, (q1c g).2.1, (q1c g).1) :=
  q1c_of_mulVec (wAl_conj_mulVec hg)

omit [CharP F 2] in
theorem q1c_transv_e₁ (s : F) : q1c (transv (e₁ F) s) = (s, 0, 0) :=
  q1c_of_mulVec fun v => by
    rw [transv_mulVec, form_e₁]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp

omit [CharP F 2] in
theorem q1c_transv_e₂ (s : F) : q1c (transv (e₂ F) s) = (0, 0, s) :=
  q1c_of_mulVec fun v => by
    rw [transv_mulVec, form_e₂]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp

omit [CharP F 2] in
theorem q1c_transv_e₁_add_e₂ (s : F) : q1c (transv (e₁ F + e₂ F) s) = (s, s, s) :=
  q1c_of_mulVec fun v => by
    rw [transv_mulVec, map_add, LinearMap.add_apply, form_e₁, form_e₂]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> ring

omit [CharP F 2] in
theorem transv_e₁_mem_Q₁ (s : F) : transv (e₁ F) s ∈ Q₁ F :=
  transv_mem_qLine isLine_ln₀ (mem_ln₀.2 ⟨by simp, by simp⟩) s

omit [CharP F 2] in
theorem transv_e₁_add_e₂_mem_Q₁ (s : F) : transv (e₁ F + e₂ F) s ∈ Q₁ F :=
  transv_mem_qLine isLine_ln₀ (mem_ln₀.2 ⟨by simp, by simp⟩) s

theorem eq_of_sq_eq {x y : F} (h : x ^ 2 = y ^ 2) : x = y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have : (x - y) ^ 2 = 0 := by linear_combination h + (y ^ 2 - x * y) * h2
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linear_combination this

variable [Finite F]

theorem levi_invariant {J : Subgroup (Sp4 F)} (hJ : J ≤ Q₁ F)
    (hJc : Nat.card J = Nat.card F ^ 2) (hν : ∀ a : F, ∀ g ∈ J, nuE a * g * (nuE a)⁻¹ ∈ J)
    (hw : ∀ g ∈ J, wAl F * g * (wAl F)⁻¹ ∈ J) :
    Nat.card F = 2 ∧ transv (e₁ F) 1 * transv (e₂ F) 1 ∈ J ∧
      transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 ∈ J := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨g₀, hg₀, hd₀⟩ : ∃ g ∈ J, (q1c g).2.2 ≠ 0 := by
    by_contra hall
    push Not at hall
    have ha : ∀ g ∈ J, (q1c g).1 = 0 := fun g hg => by
      have := hall _ (hw g hg)
      rwa [q1c_wAl_conj (hJ hg)] at this
    have hinj : Function.Injective (fun g : J => (q1c (g : Sp4 F)).2.1) := fun g h e =>
      Subtype.ext (q1c_inj (hJ g.2) (hJ h.2) (Prod.ext (by rw [ha _ g.2, ha _ h.2])
        (Prod.ext e (by rw [hall _ g.2, hall _ h.2]))))
    have := Nat.card_le_card_of_injective _ hinj
    rw [hJc] at this
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  set d := (q1c g₀).2.2 with hd
  have hk : ∀ a : F, ∃ k ∈ J, k ∈ Q₁ F ∧ q1c k = (a ^ 2 * d, a * d, 0) := fun a => by
    refine ⟨nuE a * g₀ * (nuE a)⁻¹ * g₀⁻¹, mul_mem (hν a g₀ hg₀) (inv_mem hg₀),
      mul_mem (conj_mem_Q₁ (nuE_mem_stab a) (hJ hg₀)) (inv_mem (hJ hg₀)), ?_⟩
    rw [q1c_mul (conj_mem_Q₁ (nuE_mem_stab a) (hJ hg₀)) (inv_mem (hJ hg₀)), q1c_nuE_conj (hJ hg₀),
      q1c_inv (hJ hg₀)]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hd]
  have hk' : ∀ a : F, ∃ k ∈ J, k ∈ Q₁ F ∧ q1c k = (0, a * d, a ^ 2 * d) := fun a => by
    obtain ⟨k, hkJ, hkQ, hkc⟩ := hk a
    exact ⟨wAl F * k * (wAl F)⁻¹, hw k hkJ, conj_mem_Q₁ wAl_mem_stab hkQ,
      by rw [q1c_wAl_conj hkQ, hkc]⟩
  have hu : ∀ a b : F, ∃ k ∈ J, k ∈ Q₁ F ∧ q1c k = (a ^ 2 * d, (a + b) * d, b ^ 2 * d) := by
    intro a b
    obtain ⟨k, hkJ, hkQ, hkc⟩ := hk a
    obtain ⟨k', hk'J, hk'Q, hk'c⟩ := hk' b
    refine ⟨k * k', mul_mem hkJ hk'J, mul_mem hkQ hk'Q, ?_⟩
    rw [q1c_mul hkQ hk'Q, hkc, hk'c]
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  choose u huJ huQ huc using hu
  have hsq : ∀ b : F, b ^ 2 = b := by
    intro b
    by_contra hb
    obtain ⟨k', hk'J, hk'Q, hk'c⟩ := hk' b
    set n := nuE 1 * k' * (nuE 1)⁻¹ * (u b b)⁻¹
    have hnJ : n ∈ J := mul_mem (hν 1 k' hk'J) (inv_mem (huJ b b))
    have hnQ : n ∈ Q₁ F := mul_mem (conj_mem_Q₁ (nuE_mem_stab 1) hk'Q) (inv_mem (huQ b b))
    have hnc : q1c n = (0, (b ^ 2 - b) * d, 0) := by
      rw [q1c_mul (conj_mem_Q₁ (nuE_mem_stab 1) hk'Q) (inv_mem (huQ b b)), q1c_nuE_conj hk'Q,
        q1c_inv (huQ b b), hk'c, huc]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_neg, Prod.fst_neg]
        ring
      · simp
    let f : Option (F × F) → J := fun o => match o with
      | none => ⟨n, hnJ⟩
      | some x => ⟨u x.1 x.2, huJ x.1 x.2⟩
    have hf : Function.Injective f := by
      intro o o' e
      have e' := congrArg (fun g : J => q1c (g : Sp4 F)) e
      rcases o with _ | ⟨a, b'⟩ <;> rcases o' with _ | ⟨a', b''⟩
      · rfl
      · simp only [f, hnc, huc, Prod.mk.injEq] at e'
        obtain ⟨e1, e2, e3⟩ := e'
        have ha : a' = 0 := by
          have := eq_of_sq_eq (x := a') (y := 0)
            (by rw [zero_pow two_ne_zero]; exact (mul_eq_zero.1 e1.symm).resolve_right hd₀)
          exact this
        have hb' : b'' = 0 := eq_of_sq_eq (x := b'') (y := 0)
          (by rw [zero_pow two_ne_zero]; exact (mul_eq_zero.1 e3.symm).resolve_right hd₀)
        rw [ha, hb', zero_add, zero_mul] at e2
        exact absurd (sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_right hd₀)) hb
      · simp only [f, hnc, huc, Prod.mk.injEq] at e'
        obtain ⟨e1, e2, e3⟩ := e'
        have ha : a = 0 := eq_of_sq_eq (x := a) (y := 0)
          (by rw [zero_pow two_ne_zero]; exact (mul_eq_zero.1 e1).resolve_right hd₀)
        have hb' : b' = 0 := eq_of_sq_eq (x := b') (y := 0)
          (by rw [zero_pow two_ne_zero]; exact (mul_eq_zero.1 e3).resolve_right hd₀)
        rw [ha, hb', zero_add, zero_mul] at e2
        exact absurd (sub_eq_zero.1 ((mul_eq_zero.1 e2.symm).resolve_right hd₀)) hb
      · simp only [f, huc, Prod.mk.injEq] at e'
        obtain ⟨e1, -, e3⟩ := e'
        have ha := eq_of_sq_eq (mul_right_cancel₀ hd₀ e1)
        have hb' := eq_of_sq_eq (mul_right_cancel₀ hd₀ e3)
        rw [ha, hb']
    have := Nat.card_le_card_of_injective f hf
    rw [Finite.card_option, Nat.card_prod, hJc, sq] at this
    omega
  have h01 : ∀ b : F, b = 0 ∨ b = 1 := fun b => by
    have : b * (b - 1) = 0 := by linear_combination hsq b
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hq : Nat.card F = 2 := by
    classical
    have hle : Nat.card F ≤ 2 := by
      have hinj : Function.Injective (fun b : F => if b = 0 then (0 : Fin 2) else 1) := by
        intro b b' e
        rcases h01 b with rfl | rfl <;> rcases h01 b' with rfl | rfl <;> simp_all
      simpa using Nat.card_le_card_of_injective _ hinj
    have := (Finite.one_lt_card (α := F))
    omega
  have hd1 : d = 1 := (h01 d).resolve_left hd₀
  refine ⟨hq, ?_, ?_⟩
  · have e : transv (e₁ F) 1 * transv (e₂ F) 1 = u 1 1 := by
      refine q1c_inj (mul_mem (transv_e₁_mem_Q₁ 1) (transv_e₂_mem_Q₁ 1)) (huQ 1 1) ?_
      rw [q1c_mul (transv_e₁_mem_Q₁ 1) (transv_e₂_mem_Q₁ 1), q1c_transv_e₁, q1c_transv_e₂, huc,
        hd1]
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by ring, by linear_combination -h2, by ring⟩
    rw [e]
    exact huJ 1 1
  · have e : transv (e₁ F) 1 * transv (e₁ F + e₂ F) 1 = u 0 1 := by
      refine q1c_inj (mul_mem (transv_e₁_mem_Q₁ 1) (transv_e₁_add_e₂_mem_Q₁ 1)) (huQ 0 1) ?_
      rw [q1c_mul (transv_e₁_mem_Q₁ 1) (transv_e₁_add_e₂_mem_Q₁ 1), q1c_transv_e₁,
        q1c_transv_e₁_add_e₂, huc, hd1]
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      refine ⟨by linear_combination h2, by ring, by ring⟩
    rw [e]
    exact huJ 0 1

end Levi

end CFSG.Quasithin.MS93.S5
