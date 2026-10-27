module

public import CFSG.Quasithin.H13.L32NLem1442l
public import CFSG.Quasithin.H13.L32NLem14411a
public import CFSG.Quasithin.Background.HOm4Norm

public section

namespace CFSG.Quasithin.H13.L1442

open CFSG.Fischer Matrix Mat8Cert L1442M

local instance (priority := high) decEqF4m : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def linOfAdd {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N]
    [Module (ZMod 2) N] (f : M ≃+ N) : M ≃ₗ[ZMod 2] N :=
  f.toLinearEquiv fun c x => by
    fin_cases c
    · show f ((0 : ZMod 2) • x) = (0 : ZMod 2) • f x
      rw [zero_smul, zero_smul, map_zero]
    · show f ((1 : ZMod 2) • x) = (1 : ZMod 2) • f x
      rw [one_smul, one_smul]

@[expose] noncomputable def eOf (Θ : V ≃+ Matrix (Fin 2) (Fin 2) F4) :
    V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  (Θ.trans bitsE).toLinearEquiv fun c x => by
    fin_cases c
    · show (Θ.trans bitsE) ((0 : ZMod 2) • x) = (0 : ZMod 2) • (Θ.trans bitsE) x
      rw [zero_smul, zero_smul, map_zero]
    · show (Θ.trans bitsE) ((1 : ZMod 2) • x) = (1 : ZMod 2) • (Θ.trans bitsE) x
      rw [one_smul, one_smul]

theorem eOf_apply (Θ : V ≃+ Matrix (Fin 2) (Fin 2) F4) (v : V) : eOf Θ v = bitsE (Θ v) := rfl

structure O3Data (K : Subgroup (V ≃ₗ[ZMod 2] V)) (Θ : V ≃+ Matrix (Fin 2) (Fin 2) F4) : Prop where
  fwd : ∀ γ ∈ K, ∃ A B : SpecialLinearGroup (Fin 2) F4, ∀ v,
    Θ (γ v) = (A : Matrix (Fin 2) (Fin 2) F4) * Θ v * (B : Matrix (Fin 2) (Fin 2) F4)
  bwd : ∀ A B : SpecialLinearGroup (Fin 2) F4, ∃ γ ∈ K, ∀ v,
    Θ (γ v) = (A : Matrix (Fin 2) (Fin 2) F4) * Θ v * (B : Matrix (Fin 2) (Fin 2) F4)
  card : Nat.card K = 3600

@[expose] def slT (B : SpecialLinearGroup (Fin 2) F4) : SpecialLinearGroup (Fin 2) F4 :=
  ⟨(B : Matrix (Fin 2) (Fin 2) F4)ᵀ, by rw [Matrix.det_transpose]; exact B.2⟩

theorem coe_slT (B : SpecialLinearGroup (Fin 2) F4) :
    (slT B : Matrix (Fin 2) (Fin 2) F4) = (B : Matrix (Fin 2) (Fin 2) F4)ᵀ := rfl

theorem card_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, F4.card]

theorem id_or_frob (τ : F4 ≃+* F4) : (∀ x, τ x = x) ∨ ∀ x, τ x = x * x := by
  have hω : τ F4.ω * τ F4.ω + τ F4.ω + 1 = 0 := by
    have h : F4.ω * F4.ω + F4.ω + 1 = 0 := by decide
    rw [← map_mul, ← map_one τ, ← map_add, ← map_add, h, map_zero]
  have hcase : ∀ x : F4, x * x + x + 1 = 0 → x = F4.ω ∨ x = F4.ω * F4.ω := by decide
  have h1ω : ∀ x : F4, τ (1 + x) = 1 + τ x := fun x => by rw [map_add, map_one]
  rcases hcase _ hω with h | h
  · left
    intro x
    rcases F4_cases x with rfl | rfl | rfl | rfl
    · exact map_zero τ
    · exact map_one τ
    · exact h
    · rw [h1ω, h]
  · right
    intro x
    rcases F4_cases x with rfl | rfl | rfl | rfl
    · rw [map_zero, zero_mul]
    · rw [map_one, one_mul]
    · exact h
    · rw [h1ω, h]
      decide

theorem eq_one_of_trace (δ : F4) (h : ∀ c, trF4 (δ * c) = trF4 c) : δ = 1 := by
  revert δ
  decide

theorem eq_one_of_trace_sq (δ : F4) (h : ∀ c, trF4 (δ * (c * c)) = trF4 c) : δ = 1 := by
  revert δ
  decide

namespace O3Data

variable {K : Subgroup (V ≃ₗ[ZMod 2] V)} {Θ : V ≃+ Matrix (Fin 2) (Fin 2) F4} (C : O3Data K Θ)
include C

theorem mem_map_of (A B : SpecialLinearGroup (Fin 2) F4) {g : GL (Fin 8) (ZMod 2)}
    (hg : ∀ X, bitsE ((A : Matrix (Fin 2) (Fin 2) F4) * X * (B : Matrix (Fin 2) (Fin 2) F4)) =
      (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X)) :
    g ∈ K.map (L14411.matOf (eOf Θ)) := by
  obtain ⟨γ, hγ, hγΘ⟩ := C.bwd A B
  refine ⟨γ, hγ, ?_⟩
  rw [L14411.matOf_eq_iff]
  intro v
  rw [eOf_apply, eOf_apply, hγΘ, hg]

theorem map_eq_omega3 :
    K.map (L14411.matOf (eOf Θ)) = omega3 := by
  have hl0 : (1 : F4) * 1 - 1 * 0 = 1 := by decide
  have hl1 : (0 : F4) * 0 - 1 * 1 = 1 := by decide
  have hl2 : F4.ω * (F4.ω * F4.ω) - 0 * 0 = 1 := by decide
  have hr0 : (1 : F4) * 1 - 0 * 1 = 1 := by decide
  have hle : omega3 ≤ K.map (L14411.matOf (eOf Θ)) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact C.mem_map_of (sl 1 1 0 1 hl0) 1 fun X => by
        show bitsE (!![1, 1; 0, 1] * X * 1) = _
        rw [Matrix.mul_one]; exact bitsE_o3l0 X
    · exact C.mem_map_of (sl 0 1 1 0 hl1) 1 fun X => by
        show bitsE (!![0, 1; 1, 0] * X * 1) = _
        rw [Matrix.mul_one]; exact bitsE_o3l1 X
    · exact C.mem_map_of (sl F4.ω 0 0 (F4.ω * F4.ω) hl2) 1 fun X => by
        show bitsE (!![F4.ω, 0; 0, F4.ω * F4.ω] * X * 1) = _
        rw [Matrix.mul_one]; exact bitsE_o3l2 X
    · exact C.mem_map_of 1 (sl 1 0 1 1 hr0) fun X => by
        show bitsE (1 * X * !![1, 0; 1, 1]) = _
        rw [Matrix.one_mul]; exact bitsE_o3r0 X
    · exact C.mem_map_of 1 (sl 0 1 1 0 hl1) fun X => by
        show bitsE (1 * X * !![0, 1; 1, 0]) = _
        rw [Matrix.one_mul]; exact bitsE_o3r1 X
    · exact C.mem_map_of 1 (sl F4.ω 0 0 (F4.ω * F4.ω) hl2) fun X => by
        show bitsE (1 * X * !![F4.ω, 0; 0, F4.ω * F4.ω]) = _
        rw [Matrix.one_mul]; exact bitsE_o3r2 X
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (L14411.matOf_injective _), C.card, O3Cert.card_omega3]

theorem matOf_mem_omega3N {γ : V ≃ₗ[ZMod 2] V}
    (hγ : ∀ δ, δ ∈ K ↔ γ * δ * γ⁻¹ ∈ K)
    (hγq : ∀ v, trF4 (Θ (γ v)).det = trF4 (Θ v).det) :
    L14411.matOf (eOf Θ) γ ∈ omega3N := by
  classical
  let toM : (V ≃ₗ[ZMod 2] V) → MulAut (H.Om4.VM F4) := fun ψ =>
    AddEquiv.toMultiplicative (Θ.symm.trans (ψ.toAddEquiv.trans Θ))
  let ofM : MulAut (H.Om4.VM F4) → (V ≃ₗ[ZMod 2] V) := fun h =>
    linOfAdd ((Θ.trans (AddEquiv.toMultiplicative.symm h)).trans Θ.symm)
  have htoM : ∀ ψ (X : H.Om4.VM F4), toM ψ X =
      Multiplicative.ofAdd (Θ (ψ (Θ.symm (Multiplicative.toAdd X)))) := fun _ _ => rfl
  have hofM : ∀ h v, ofM h v =
      Θ.symm (Multiplicative.toAdd (h (Multiplicative.ofAdd (Θ v)))) := fun _ _ => rfl
  have hinvγ : ∀ w, γ (γ⁻¹ w) = w := fun w => γ.apply_symm_apply w
  have hinvγ' : ∀ w, γ⁻¹ (γ w) = w := fun w => γ.symm_apply_apply w
  have hrange : ∀ h : MulAut (H.Om4.VM F4), h ∈ (H.Om4.rho (K := F4)).range ↔ ofM h ∈ K := by
    intro h
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨δ, hδ, hδΘ⟩ := C.bwd z.1 (slT z.2)
      have : ofM (H.Om4.rho z) = δ := by
        ext v
        apply Θ.injective
        rw [hofM, AddEquiv.apply_symm_apply, H.Om4.rho_apply, H.Om4.toAdd_lr, toAdd_ofAdd, hδΘ,
          coe_slT, SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix]
      rw [this]
      exact hδ
    · intro hK
      obtain ⟨A, B, hAB⟩ := C.fwd _ hK
      refine ⟨(A, slT B), MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_⟩
      rw [H.Om4.rho_apply, H.Om4.toAdd_lr, SpecialLinearGroup.coe_GL_coe_matrix,
        SpecialLinearGroup.coe_GL_coe_matrix, coe_slT, Matrix.transpose_transpose]
      have h1 := hAB (Θ.symm (Multiplicative.toAdd X))
      rw [hofM, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ofAdd_toAdd] at h1
      exact h1.symm
  have e1 : (toM γ)⁻¹ = toM γ⁻¹ := by
    refine inv_eq_of_mul_eq_one_right (MulEquiv.ext fun X => ?_)
    rw [MulAut.mul_apply, htoM, htoM, toAdd_ofAdd, AddEquiv.symm_apply_apply, hinvγ,
      AddEquiv.apply_symm_apply, ofAdd_toAdd, MulAut.one_apply]
  have hconj : ∀ h : MulAut (H.Om4.VM F4), ofM (toM γ * h * (toM γ)⁻¹) = γ * ofM h * γ⁻¹ := by
    intro h
    ext v
    apply Θ.injective
    rw [hofM, AddEquiv.apply_symm_apply, e1, MulAut.mul_apply, MulAut.mul_apply, htoM, htoM,
      toAdd_ofAdd, toAdd_ofAdd, AddEquiv.symm_apply_apply]
    show Θ (γ (Θ.symm (Multiplicative.toAdd (h (Multiplicative.ofAdd (Θ (γ⁻¹ v))))))) =
      Θ (γ (ofM h (γ⁻¹ v)))
    rw [hofM]
  have hnorm : toM γ ∈ Subgroup.normalizer ((H.Om4.rho (K := F4)).range :
      Set (MulAut (H.Om4.VM F4))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hrange, hrange, hconj, ← hγ]
  have h4 : 4 ≤ Nat.card F4 := card_F4.ge
  obtain ⟨A, B, τ, hy⟩ := H.Om4.exists_eq_of_mem_normalizer h4 hnorm
  have hγy : ∀ X, Θ (γ (Θ.symm X)) = Multiplicative.toAdd (toM γ (Multiplicative.ofAdd X)) :=
    fun X => (htoM γ X).symm
  have hF : o3field ∈ omega3N := Subgroup.subset_closure (by simp)
  have hS : o3swap ∈ omega3N := Subgroup.subset_closure (by simp)
  have hmapτ : ∀ X : Matrix (Fin 2) (Fin 2) F4, (X.map τ).det = τ X.det := fun X =>
    (RingHom.map_det τ.toRingHom X).symm
  obtain ⟨T, gT, hgT, hTbits, hTdet, hTy⟩ : ∃ (T : Matrix (Fin 2) (Fin 2) F4 →
      Matrix (Fin 2) (Fin 2) F4) (gT : GL (Fin 8) (ZMod 2)), gT ∈ omega3N ∧
      (∀ X, bitsE (T X) = (gT : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X)) ∧
      (∀ X, (T X).det = τ X.det) ∧
      ∀ X, Θ (γ (Θ.symm X)) = (A : Matrix (Fin 2) (Fin 2) F4) * T X *
        (B : Matrix (Fin 2) (Fin 2) F4)ᵀ := by
    rcases hy with hy | hy
    · refine ⟨fun X => X.map τ, ?_⟩
      have hT : ∀ X, Θ (γ (Θ.symm X)) = (A : Matrix (Fin 2) (Fin 2) F4) * X.map τ *
          (B : Matrix (Fin 2) (Fin 2) F4)ᵀ := fun X => by
        rw [hγy, hy, MulAut.mul_apply, H.Om4.toAdd_lr, H.Om4.toAdd_frM]
        rfl
      rcases id_or_frob τ with hτ | hτ
      · have hm : ∀ X : Matrix (Fin 2) (Fin 2) F4, X.map τ = X := fun X => by
          ext i j; exact hτ _
        exact ⟨1, one_mem _, fun X => by
          show bitsE (X.map τ) = _
          rw [hm, Units.val_one, Matrix.one_mulVec], hmapτ, hT⟩
      · have hm : ∀ X : Matrix (Fin 2) (Fin 2) F4, X.map τ = X.map fun x => x * x := fun X => by
          ext i j; exact hτ _
        exact ⟨o3field, hF, fun X => by
          show bitsE (X.map τ) = _
          rw [hm, bitsE_field], hmapτ, hT⟩
    · refine ⟨fun X => Xᵀ.map τ, ?_⟩
      have hT : ∀ X, Θ (γ (Θ.symm X)) = (A : Matrix (Fin 2) (Fin 2) F4) * Xᵀ.map τ *
          (B : Matrix (Fin 2) (Fin 2) F4)ᵀ := fun X => by
        rw [hγy, hy, MulAut.mul_apply, MulAut.mul_apply, H.Om4.toAdd_lr, H.Om4.toAdd_frM,
          H.Om4.toAdd_trM]
        rfl
      have hdet : ∀ X : Matrix (Fin 2) (Fin 2) F4, (Xᵀ.map τ).det = τ X.det := fun X => by
        rw [hmapτ, Matrix.det_transpose]
      rcases id_or_frob τ with hτ | hτ
      · have hm : ∀ X : Matrix (Fin 2) (Fin 2) F4, Xᵀ.map τ = Xᵀ := fun X => by
          ext i j; exact hτ _
        exact ⟨o3swap, hS, fun X => by
          show bitsE (Xᵀ.map τ) = _
          rw [hm, bitsE_swap], hdet, hT⟩
      · have hm : ∀ X : Matrix (Fin 2) (Fin 2) F4, Xᵀ.map τ = Xᵀ.map fun x => x * x :=
          fun X => by ext i j; exact hτ _
        refine ⟨o3field * o3swap, Subgroup.mul_mem _ hF hS, fun X => ?_, hdet, hT⟩
        show bitsE (Xᵀ.map τ) = _
        rw [hm, bitsE_field, bitsE_swap, Units.val_mul, Matrix.mulVec_mulVec]
  have hδ : (A : Matrix (Fin 2) (Fin 2) F4).det * (B : Matrix (Fin 2) (Fin 2) F4).det = 1 := by
    have hc : ∀ c : F4, trF4 ((A : Matrix (Fin 2) (Fin 2) F4).det *
        (B : Matrix (Fin 2) (Fin 2) F4).det * τ c) = trF4 c := by
      intro c
      have h1 := hγq (Θ.symm !![c, 0; 0, 1])
      rw [hTy, AddEquiv.apply_symm_apply, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        hTdet, Matrix.det_fin_two_of] at h1
      simp only [mul_one, mul_zero, sub_zero] at h1
      rw [← h1]
      congr 1
      ring
    rcases id_or_frob τ with hτ | hτ
    · exact eq_one_of_trace _ fun c => by have := hc c; rwa [hτ c] at this
    · exact eq_one_of_trace_sq _ fun c => by have := hc c; rwa [hτ c] at this
  have hu0 : (A : Matrix (Fin 2) (Fin 2) F4).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hδ
    exact zero_ne_one hδ
  obtain ⟨c, hc2, hc0⟩ : ∃ c : F4, c * c = ((A : Matrix (Fin 2) (Fin 2) F4).det)⁻¹ ∧ c ≠ 0 := by
    refine ⟨((A : Matrix (Fin 2) (Fin 2) F4).det)⁻¹ * ((A : Matrix (Fin 2) (Fin 2) F4).det)⁻¹,
      ?_, mul_ne_zero (inv_ne_zero hu0) (inv_ne_zero hu0)⟩
    have h := F4.sq_sq ((A : Matrix (Fin 2) (Fin 2) F4).det)⁻¹
    rw [sq, sq] at h
    exact h
  have hA' : (c • (A : Matrix (Fin 2) (Fin 2) F4)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, sq, hc2, inv_mul_cancel₀ hu0]
  have hB' : (c⁻¹ • (B : Matrix (Fin 2) (Fin 2) F4)ᵀ).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_transpose, sq, ← mul_inv, hc2, inv_inv, hδ]
  obtain ⟨δ₁, hδ₁, hδ₁Θ⟩ := C.bwd ⟨_, hA'⟩ ⟨_, hB'⟩
  have hg₁ : L14411.matOf (eOf Θ) δ₁ ∈ omega3 := by
    rw [← C.map_eq_omega3]
    exact ⟨δ₁, hδ₁, rfl⟩
  have hmem3 : omega3 ≤ omega3N := Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  have heq : L14411.matOf (eOf Θ) γ = L14411.matOf (eOf Θ) δ₁ * gT := by
    rw [L14411.matOf_eq_iff]
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, eOf_apply, eOf_apply, ← hTbits]
    have h1 : bitsE (T (Θ v)) = eOf Θ (Θ.symm (T (Θ v))) := by
      rw [eOf_apply, AddEquiv.apply_symm_apply]
    rw [h1, L14411.matOf_mulVec, eOf_apply, hδ₁Θ, AddEquiv.apply_symm_apply]
    congr 1
    show Θ (γ v) = c • (A : Matrix (Fin 2) (Fin 2) F4) * T (Θ v) * (c⁻¹ • (B :
      Matrix (Fin 2) (Fin 2) F4)ᵀ)
    have h2 := hTy (Θ v)
    rw [AddEquiv.symm_apply_apply] at h2
    rw [h2]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [heq]
  exact Subgroup.mul_mem _ (hmem3 hg₁) hgT

end O3Data

end CFSG.Quasithin.H13.L1442
