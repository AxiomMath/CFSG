module

public import CFSG.Quasithin.H13.L32AL2s
public import CFSG.Quasithin.EmptyFaithful.S153G93DOm4PB
public import CFSG.Quasithin.Background.HOm4UT

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

section F4

variable [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem exists_omega (h4 : Nat.card F = 4) :
    ∃ ω : F, ω * ω + ω + 1 = 0 ∧ ∀ c : F, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω * ω := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, h4]
  have hquad : ∀ c : F, c ≠ 0 → c ≠ 1 → c * c + c + 1 = 0 := fun c hc0 hc1 => by
    have h3 : c ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one c hc0
      rwa [hcard] at this
    have h : (c - 1) * (c * c + c + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hc1
    · exact h
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun c _ => by
      by_cases hc : c = 0
      · simp [hc]
      · simp [hall c hc]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at h1
    have h2 : ({0, 1} : Finset F).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hω := hquad ω hω0 hω1
  refine ⟨ω, hω, fun c => ?_⟩
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  by_cases hc1 : c = 1
  · exact Or.inr (Or.inl hc1)
  have hc := hquad c hc0 hc1
  have h : (c - ω) * (c - ω * ω) = 0 := by linear_combination hc + (ω - c - 1) * hω
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

omit [CharP F 2] in
theorem ringEquiv_cases (h4 : Nat.card F = 4) (τ : F ≃+* F) :
    τ = 1 ∨ ∀ c : F, τ c = c * c := by
  obtain ⟨ω, hω, hall⟩ := exists_omega h4
  have hτω : τ ω * τ ω + τ ω + 1 = 0 := by
    have := congrArg τ hω
    rwa [map_add, map_add, map_mul, map_one, map_zero] at this
  have h : (τ ω - ω) * (τ ω - ω * ω) = 0 := by
    linear_combination hτω + (ω - τ ω - 1) * hω
  rcases mul_eq_zero.mp h with h | h
  · left
    have hτ : τ ω = ω := sub_eq_zero.mp h
    refine RingEquiv.ext fun c => ?_
    rcases hall c with rfl | rfl | rfl | rfl
    · exact map_zero τ
    · exact map_one τ
    · exact hτ
    · rw [map_mul, hτ]
      rfl
  · right
    have hτ : τ ω = ω * ω := sub_eq_zero.mp h
    intro c
    rcases hall c with rfl | rfl | rfl | rfl
    · rw [map_zero, mul_zero]
    · rw [map_one, mul_one]
    · exact hτ
    · rw [map_mul, hτ]

end F4

@[expose] def IsSemi (x : MulAut (VM F)) (τ : F ≃+* F) : Prop :=
  ∀ (c : F) (X : Matrix (Fin 2) (Fin 2) F),
    Multiplicative.toAdd (x (Multiplicative.ofAdd (c • X))) =
      τ c • Multiplicative.toAdd (x (Multiplicative.ofAdd X))

theorem isSemi_lr_frM (A B : GL (Fin 2) F) (τ : F ≃+* F) : IsSemi (lr A B * frM τ) τ := by
  intro c X
  rw [MulAut.mul_apply, MulAut.mul_apply, toAdd_lr, toAdd_lr, toAdd_frM, toAdd_frM, toAdd_ofAdd,
    toAdd_ofAdd]
  have : (c • X).map τ = τ c • X.map τ := by
    ext i j
    simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isSemi_trM : IsSemi (trM : MulAut (VM F)) 1 := by
  intro c X
  rw [toAdd_trM, toAdd_trM, toAdd_ofAdd, toAdd_ofAdd, Matrix.transpose_smul]
  rfl

theorem IsSemi.mul {x y : MulAut (VM F)} {τ σ : F ≃+* F} (hx : IsSemi x τ) (hy : IsSemi y σ) :
    IsSemi (x * y) (τ * σ) := by
  intro c X
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have h1 := hy c X
  have h2 : y (Multiplicative.ofAdd (c • X)) =
      Multiplicative.ofAdd (σ c • Multiplicative.toAdd (y (Multiplicative.ofAdd X))) := by
    rw [← h1, ofAdd_toAdd]
  rw [h2, hx, ofAdd_toAdd]
  rfl

theorem IsSemi.inv {x : MulAut (VM F)} {τ : F ≃+* F} (hx : IsSemi x τ) : IsSemi x⁻¹ τ⁻¹ := by
  intro c X
  have h := hx (τ⁻¹ c) (Multiplicative.toAdd (x⁻¹ (Multiplicative.ofAdd X)))
  rw [ofAdd_toAdd, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, toAdd_ofAdd] at h
  have e : τ (τ⁻¹ c) = c := τ.apply_symm_apply c
  rw [e] at h
  have h' : x (Multiplicative.ofAdd (τ⁻¹ c • Multiplicative.toAdd (x⁻¹ (Multiplicative.ofAdd X)))) =
      Multiplicative.ofAdd (c • X) := by
    rw [← ofAdd_toAdd (x _), h]
  have h'' := congrArg (fun v : VM F => (x⁻¹ : MulAut (VM F)) v) h'
  simp only [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h''
  rw [← h'', toAdd_ofAdd]

theorem isSemi_lr_frM_trM (A B : GL (Fin 2) F) (τ : F ≃+* F) :
    IsSemi (lr A B * frM τ * trM) τ := by
  have := (isSemi_lr_frM A B τ).mul isSemi_trM
  rwa [mul_one] at this

theorem isSemi_of_mem_normalizer [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {x : MulAut (VM F)}
    (hx : x ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F)))) :
    ∃ τ : F ≃+* F, IsSemi x τ := by
  obtain ⟨A, B, τ, h | h⟩ := exists_eq_of_mem_normalizer h4 hx
  · exact ⟨τ, h ▸ isSemi_lr_frM A B τ⟩
  · exact ⟨τ, h ▸ isSemi_lr_frM_trM A B τ⟩

theorem IsSemi.eq {x : MulAut (VM F)} {τ σ : F ≃+* F} (hx : IsSemi x τ) (hy : IsSemi x σ) :
    τ = σ := by
  have hne :
      Multiplicative.toAdd (x (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F))) ≠ 0 := by
    intro h0
    have e : x (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F)) = x 1 := by
      rw [map_one x]
      exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
    have h1 : (1 : Matrix (Fin 2) (Fin 2) F) = 0 := congrArg Multiplicative.toAdd (x.injective e)
    exact one_ne_zero h1
  exact RingEquiv.ext fun c => smul_left_injective F hne ((hx c 1).symm.trans (hy c 1))

theorem IsSemi.conj {x y : MulAut (VM F)} {τ : F ≃+* F} (hx : IsSemi x τ) (hy : IsSemi y 1) :
    IsSemi (x * y * x⁻¹) 1 := by
  have := (hx.mul hy).mul hx.inv
  rwa [mul_one, mul_inv_cancel] at this

@[expose] def smulM (c : F) (hc : c ≠ 0) : MulAut (VM F) where
  toFun X := Multiplicative.ofAdd (c • Multiplicative.toAdd X)
  invFun X := Multiplicative.ofAdd (c⁻¹ • Multiplicative.toAdd X)
  left_inv X := by simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv X := by simp [smul_smul, mul_inv_cancel₀ hc]
  map_mul' X Y := by simp [smul_add]

theorem toAdd_smulM (c : F) (hc : c ≠ 0) (X : VM F) :
    Multiplicative.toAdd (smulM c hc X) = c • Multiplicative.toAdd X := rfl

theorem card_vm (h4 : Nat.card F = 4) : Nat.card (VM F) = 256 := by
  rw [show Nat.card (VM F) = Nat.card (Matrix (Fin 2) (Fin 2) F) from
    Nat.card_congr Multiplicative.toAdd]
  change Nat.card (Fin 2 → Fin 2 → F) = 256
  rw [Nat.card_fun, Nat.card_fun, h4, Nat.card_fin]
  norm_num

theorem card_ker_of_semi [Finite F] [CharP F 2] (h4 : Nat.card F = 4) {x : MulAut (VM F)}
    {τ : F ≃+* F} (hx : IsSemi x τ) (hτ : τ ≠ 1) (hx2 : x * x = 1) :
    Nat.card (commHom x).ker = 16 := by
  obtain ⟨ω, hω, -⟩ := exists_omega h4
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hτω : τ ω = ω * ω := by
    rcases ringEquiv_cases h4 τ with h | h
    · exact absurd h hτ
    · exact h ω
  set s := smulM ω hω0 with hs_def
  have hV : ∀ w : VM F, w * w = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hs : ∀ w, s w * s (s w) * w = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_mul, toAdd_one, hs_def, toAdd_smulM, toAdd_smulM, toAdd_smulM, smul_smul]
    rw [show ω • Multiplicative.toAdd w + (ω * ω) • Multiplicative.toAdd w +
        Multiplicative.toAdd w = (ω * ω + ω + 1) • Multiplicative.toAdd w by
      rw [add_smul, add_smul, one_smul]
      abel, hω, zero_smul]
  have hfs : x * s = s * s * x := by
    refine MulEquiv.ext fun w => Multiplicative.toAdd.injective ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hs_def, toAdd_smulM, toAdd_smulM]
    have h1 := hx ω (Multiplicative.toAdd w)
    rw [ofAdd_toAdd] at h1
    change Multiplicative.toAdd (x (Multiplicative.ofAdd (ω • Multiplicative.toAdd w))) = _
    rw [h1, hτω, smul_smul]
  have h := card_ker_sq_of_semilinear hV hs hx2 hfs
  rw [card_vm h4] at h
  have h16 : (16 : ℕ) ^ 2 = 256 := by norm_num
  rw [← h16] at h
  exact Nat.pow_left_injective (by norm_num) h

theorem commV_zpowers_eq_range {W' : Type} [CommGroup W'] {x : MulAut W'} (hx2 : x * x = 1) :
    CFSG.Quasithin.commV (Subgroup.zpowers x) = (commHom x).range := by
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hpow : ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := by
    intro k
    refine Int.induction_on k (Or.inl (zpow_zero x)) (fun n ih => ?_) (fun n ih => ?_)
    · rw [_root_.zpow_add_one]
      rcases ih with h | h <;> rw [h] <;> simp [hx2]
    · rw [_root_.zpow_sub_one, hinv]
      rcases ih with h | h <;> rw [h] <;> simp [hx2]
  apply le_antisymm
  · rw [CFSG.Quasithin.commV, Subgroup.closure_le]
    rintro w ⟨y, hy, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases hpow k with h | h
    · rw [h, MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    · rw [h]
      exact ⟨v, rfl⟩
  · rintro w ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, v, rfl⟩

@[expose] def matJ : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

theorem eq_inv_of_sq [CharP F 2] {A B : GL (Fin 2) F} (h : (lr A B * trM) * (lr A B * trM) = 1) :
    B = A⁻¹ := by
  have e : (lr A B * trM) * (lr A B * trM) = lr (A * B) (B * A) := by
    calc (lr A B * trM) * (lr A B * trM) = lr A B * (trM * lr A B) * trM := by group
      _ = lr A B * lr B A * (trM * trM) := by rw [trM_lr]; group
      _ = _ := by rw [trM_mul_self, mul_one, lr_mul]
  rw [e] at h
  have key : ∀ X : Matrix (Fin 2) (Fin 2) F,
      ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X *
        ((B * A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ = X := by
    intro X
    have := congrArg (fun f : MulAut (VM F) => Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa [toAdd_lr] using this
  set P : Matrix (Fin 2) (Fin 2) F := ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hP
  set Q : Matrix (Fin 2) (Fin 2) F := ((B * A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hQ
  have hPQ : P * Qᵀ = 1 := by simpa using key 1
  have hQP : Qᵀ * P = 1 := mul_eq_one_comm.mp hPQ
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) F, Commute X P := by
    intro X
    have h1 := key X
    calc X * P = P * X * Qᵀ * P := by rw [h1]
      _ = P * X := by rw [Matrix.mul_assoc (P * X), hQP, Matrix.mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  have hPc : P = c • 1 := by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hQc : Q = c • 1 := by
    have hA : ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
        1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e1 : Q = ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * P *
        (A : Matrix (Fin 2) (Fin 2) F) := by
      rw [hQ, hP]
      simp only [Units.val_mul]
      rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), hA, Matrix.one_mul]
    rw [e1, hPc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hA]
  have hc2 : c * c = 1 := by
    have := congrFun (congrFun hPQ 0) 0
    rw [hPc, hQc, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one] at this
    simpa [smul_smul] using this
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc1 : c = 1 := by
    have h3 : (c + 1) * (c + 1) = 0 := by linear_combination hc2 + (c + 1) * h2
    linear_combination mul_self_eq_zero.mp h3 - h2
  have hAB : A * B = 1 := Units.ext (by rw [← hP, hPc, hc1, one_smul]; rfl)
  exact eq_inv_of_mul_eq_one_right hAB

theorem inv_cases [Finite F] [CharP F 2] (h4 : Nat.card F = 4) {x : MulAut (VM F)}
    (hx : x ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    16 ≤ Nat.card (commHom x).range ∨ ∃ A : GL (Fin 2) F, x = lr A A⁻¹ * trM := by
  obtain ⟨A, B, τ, h | h⟩ := exists_eq_of_mem_normalizer (by omega) hx
  · left
    have ha : congrHom (MulEquiv.refl (VM F)) x = lr A B * frM τ := by
      rw [← h]
      exact MulEquiv.ext fun _ => rfl
    have hx2' : (lr A B * frM τ) * (lr A B * frM τ) = 1 := h ▸ hx2
    have hx1' : lr A B * frM τ ≠ 1 := h ▸ hx1
    have h1 := S153G93D.Om4P.card_le_commV (MulEquiv.refl (VM F)) ha
      (S153G93D.Om4P.not_scalar hx2' hx1')
    rw [commV_zpowers_eq_range hx2, h4] at h1
    exact le_of_eq_of_le (by norm_num) h1
  · by_cases hτ : τ = 1
    · right
      subst hτ
      rw [frM_one, mul_one] at h
      have hx2' : (lr A B * trM) * (lr A B * trM) = 1 := h ▸ hx2
      refine ⟨A, ?_⟩
      rw [h, eq_inv_of_sq hx2']
    · left
      have hs : IsSemi x τ := h ▸ isSemi_lr_frM_trM A B τ
      have hk := card_ker_of_semi h4 hs hτ hx2
      have hc := card_ker_mul_card_range x
      rw [hk, card_vm h4] at hc
      omega

theorem mem_range_commHom_iff [CharP F 2] (A : GL (Fin 2) F) (w : VM F) :
    w ∈ (commHom (lr A A⁻¹ * trM)).range ↔
      ∃ c : F, w = Multiplicative.ofAdd (c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hM
  set N : Matrix (Fin 2) (Fin 2) F := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ Y : Matrix (Fin 2) (Fin 2) F,
      Multiplicative.toAdd (commHom (lr A A⁻¹ * trM) (Multiplicative.ofAdd (M * Y))) =
        (Y 1 0 + Y 0 1) • (M * matJ) := by
    intro Y
    rw [commHom_apply, toAdd_mul, toAdd_inv, MulAut.mul_apply, toAdd_lr, toAdd_trM, toAdd_ofAdd]
    rw [← hM, ← hN, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.transpose_mul, hNM, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_neg,
      ← Matrix.mul_add, ← Matrix.mul_smul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matJ, CharTwo.neg_eq, add_comm, CharTwo.add_self_eq_zero]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(N * Multiplicative.toAdd v) 1 0 + (N * Multiplicative.toAdd v) 0 1, ?_⟩
    apply Multiplicative.toAdd.injective
    have e : v = Multiplicative.ofAdd (M * (N * Multiplicative.toAdd v)) := by
      rw [← Matrix.mul_assoc, hMN, Matrix.one_mul, ofAdd_toAdd]
    rw [toAdd_ofAdd, ← key, ← e]
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd (M * Matrix.of ![![0, 0], ![c, 0]]), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [key, toAdd_ofAdd]
    simp

end CFSG.Quasithin.H13.L32A.L2
