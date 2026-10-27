module

public import CFSG.Quasithin.Vol2.Ch12Sec6L24a

public section

namespace CFSG.Quasithin.H13.F126

open CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F S126FE S126L19 S126L24
  Equiv

@[expose] def blP : Perm (Fin 4) × Perm (Fin 4) →* Perm (Fin 8) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Perm.sumCongrHom (Fin 4) (Fin 4))

theorem blP_injective : Function.Injective blP :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Perm.sumCongrHom_injective

theorem exists_blP {σ : Perm (Fin 8)} (h : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) :
    ∃ p, blP p = σ := by
  set σ' : Perm (Fin 4 ⊕ Fin 4) := (Equiv.permCongrHom finSumFinEquiv).symm σ with hσ'
  have hmaps : Set.MapsTo σ' (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨a, rfl⟩
    have h1 : ((finSumFinEquiv (m := 4) (n := 4) (Sum.inl a)) : Fin 8).val < 4 := by
      rw [finSumFinEquiv_apply_left, Fin.val_castAdd]
      exact a.isLt
    have h2 := (h _).1 h1
    have e : σ' (Sum.inl a) = finSumFinEquiv.symm (σ (finSumFinEquiv (m := 4) (n := 4)
        (Sum.inl a))) := rfl
    rw [e]
    set j := σ (finSumFinEquiv (m := 4) (n := 4) (Sum.inl a)) with hj
    refine ⟨⟨j.val, h2⟩, ?_⟩
    apply finSumFinEquiv.injective
    rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
    rfl
  obtain ⟨p, hp⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  refine ⟨p, ?_⟩
  rw [blP, MonoidHom.comp_apply, hp, hσ']
  exact MulEquiv.apply_symm_apply _ σ

@[expose] def ActEq (τ σ : Perm (Fin 8)) : Prop := ∀ y ∈ W5, dAct τ y * (dAct σ y)⁻¹ ∈ W1

@[expose] def ActFpf (σ : Perm (Fin 8)) : Prop := ∀ y ∈ W5, dAct σ y * y⁻¹ ∈ W1 → y ∈ W1

abbrev S8 (x : Fin 8 → ZMod 2) : ZMod 2 := x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7

@[expose] def ofVec (x : Fin 8 → ZMod 2) (hx : S8 x = 0) : ↥(coreMod 8) :=
  ⟨Multiplicative.ofAdd x, mem_coreMod.2 (by rw [Fin.sum_univ_eight]; exact hx)⟩

theorem vx_ofVec (x : Fin 8 → ZMod 2) (hx : S8 x = 0) : vx (ofVec x hx) = x := rfl

theorem actEq_iff (τ σ : Perm (Fin 8)) : ActEq τ σ ↔
    ∀ x : Fin 8 → ZMod 2, S8 x = 0 → Ev x → BC (fun i => x (τ⁻¹ i) - x (σ⁻¹ i)) := by
  constructor
  · intro h x hx hev
    have h1 := h _ ((mem_W5_iff (ofVec x hx)).2 hev)
    rw [dAct_mk, dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul,
      vx_inv, vx_coreAct, vx_coreAct, vx_ofVec, ← sub_eq_add_neg] at h1
    exact h1
  · intro h y hy
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [dAct_mk, dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul,
      vx_inv, vx_coreAct, vx_coreAct, ← sub_eq_add_neg]
    exact h (vx m) (sum8 m) ((mem_W5_iff m).1 hy)

theorem actFpf_iff (σ : Perm (Fin 8)) : ActFpf σ ↔
    ∀ x : Fin 8 → ZMod 2, S8 x = 0 → Ev x → BC (fun i => x (σ⁻¹ i) - x i) → BC x := by
  constructor
  · intro h x hx hev hbc
    have h1 := h _ ((mem_W5_iff (ofVec x hx)).2 hev)
    rw [dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul,
      vx_inv, vx_coreAct, vx_ofVec, ← sub_eq_add_neg, mem_W1_iff, vx_ofVec] at h1
    exact h1 hbc
  · intro h y hy hfix
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul,
      vx_inv, vx_coreAct, ← sub_eq_add_neg] at hfix
    rw [mem_W1_iff]
    exact h (vx m) (sum8 m) ((mem_W5_iff m).1 hy) hfix

@[expose] def CHypA (σ : Perm (Fin 8)) (k : Bool) : Prop :=
  ∀ x : Fin 8 → ZMod 2, S8 x = 0 ∧ Ev x →
    BC (fun i => x ((S126L1c.bsw * σ * S126L1c.bsw⁻¹)⁻¹ i) - x ((σ ^ (if k then 1 else 2))⁻¹ i))

@[expose] def CHypB (σ : Perm (Fin 8)) : Prop :=
  ∃ x : Fin 8 → ZMod 2, S8 x = 0 ∧ Ev x ∧ ¬ BC (fun i => x (σ⁻¹ i) - x i)

@[expose] def CConcl (σ : Perm (Fin 8)) : Prop :=
  ∀ x : Fin 8 → ZMod 2, S8 x = 0 ∧ Ev x ∧ BC (fun i => x (σ⁻¹ i) - x i) → BC x

instance (σ : Perm (Fin 8)) (k : Bool) : Decidable (CHypA σ k) := by
  unfold CHypA; infer_instance

instance (σ : Perm (Fin 8)) : Decidable (CHypB σ) := by
  unfold CHypB; infer_instance

instance (σ : Perm (Fin 8)) : Decidable (CConcl σ) := by
  unfold CConcl; infer_instance

theorem check_fpf : ∀ σ₁ : Perm (Fin 4), σ₁ ^ 3 = 1 → ∀ σ₂ : Perm (Fin 4), σ₂ ^ 3 = 1 →
    ∀ k : Bool, CHypA (blP (σ₁, σ₂)) k ∧ CHypB (blP (σ₁, σ₂)) → CConcl (blP (σ₁, σ₂)) := by
  decide +kernel

theorem actFpf_of_conj {σ : Perm (Fin 8)} (hblock : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4))
    (h3 : σ ^ 3 = 1)
    (hk : ActEq (S126L1c.bsw * σ * S126L1c.bsw⁻¹) σ ∨
      ActEq (S126L1c.bsw * σ * S126L1c.bsw⁻¹) (σ ^ 2))
    (hnt : ¬ ActEq σ 1) : ActFpf σ := by
  obtain ⟨⟨σ₁, σ₂⟩, rfl⟩ := exists_blP hblock
  have h3' : blP (σ₁ ^ 3, σ₂ ^ 3) = blP 1 := by
    rw [← Prod.pow_mk, map_pow, h3, map_one]
  have h3'' := Prod.ext_iff.1 (blP_injective h3')
  have hnt' : ∃ x : Fin 8 → ZMod 2, S8 x = 0 ∧ Ev x ∧
      ¬ BC (fun i => x ((blP (σ₁, σ₂))⁻¹ i) - x i) := by
    by_contra hno
    push Not at hno
    apply hnt
    rw [actEq_iff]
    intro x hx hev
    simpa using hno x hx hev
  rw [actFpf_iff]
  intro x hx hev hbc
  rcases hk with hk | hk
  · rw [actEq_iff] at hk
    exact check_fpf σ₁ h3''.1 σ₂ h3''.2 true
      ⟨fun x hx => by simpa using hk x hx.1 hx.2, hnt'⟩ x ⟨hx, hev, hbc⟩
  · rw [actEq_iff] at hk
    exact check_fpf σ₁ h3''.1 σ₂ h3''.2 false
      ⟨fun x hx => by simpa [CHypA] using hk x hx.1 hx.2, hnt'⟩ x ⟨hx, hev, hbc⟩

@[expose] def c4 : Perm (Fin 4) := swap 0 1 * swap 1 2

@[expose] def aP : Perm (Fin 8) := blP (c4, 1)

@[expose] def bP : Perm (Fin 8) := blP (1, c4)

theorem aP_mem : aP ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem bP_mem : bP ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem aP_pow_three : aP ^ 3 = 1 := by decide

theorem bP_pow_three : bP ^ 3 = 1 := by decide

theorem aP_block : ∀ i : Fin 8, (i.val < 4 ↔ (aP i).val < 4) := by decide

theorem bP_block : ∀ i : Fin 8, (i.val < 4 ↔ (bP i).val < 4) := by decide

theorem check_indep : ∀ i j : Fin 3,
    (∀ x : Fin 8 → ZMod 2, S8 x = 0 ∧ Ev x →
      BC (fun k => x ((aP ^ i.val * bP ^ j.val)⁻¹ k) - x k)) → i = 0 ∧ j = 0 := by
  decide +kernel

theorem indep_ab {i j : Fin 3} (h : ActEq (aP ^ i.val * bP ^ j.val) 1) : i = 0 ∧ j = 0 := by
  rw [actEq_iff] at h
  exact check_indep i j fun x hx => by simpa using h x hx.1 hx.2

end CFSG.Quasithin.H13.F126
