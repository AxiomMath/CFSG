module

public import CFSG.Quasithin.Background.JonesParshallSL2

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Assembly.LowTwoRank

section KerBot

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def secEquivSub (D : FFModel) (hk : D.ker = ⊥) : D.Sec ≃* ↥D.sec :=
  MulEquiv.ofBijective (QuotientGroup.lift _ (MonoidHom.id _) fun x hx => by
      rw [Subgroup.mem_subgroupOf, hk, Subgroup.mem_bot] at hx
      exact Subtype.ext hx)
    ⟨fun x y hxy => by
      induction x using QuotientGroup.induction_on with
      | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hxy
      exact congrArg _ hxy,
    fun m => ⟨QuotientGroup.mk m, rfl⟩⟩

theorem secEquivSub_mk (D : FFModel) (hk : D.ker = ⊥) (m : ↥D.sec) :
    secEquivSub D hk (QuotientGroup.mk m) = m :=
  rfl

theorem Witness.sub {D : FFModel} (hk : D.ker = ⊥) {ρ : Representation (ZMod 2) Γ W}
    {θ : Γ ≃* D.Gam} {β : W ≃+ Additive D.Sec} (h : D.Witness ρ θ β) (γ : Γ) (w : W) :
    ((Additive.toMul ((β.trans (secEquivSub D hk).toAdditive) (ρ γ w)) : ↥D.sec) : D.Amb) =
      D.act (θ γ) ((Additive.toMul ((β.trans (secEquivSub D hk).toAdditive) w) : ↥D.sec) :
        D.Amb) := by
  obtain ⟨-, hsec, -, hint⟩ := h
  set e := secEquivSub D hk
  let m : ↥D.sec := e (Additive.toMul (β w))
  have hm : D.act (θ γ) m ∈ D.sec := hsec _ _ m.2
  have hw : β w = Additive.ofMul (QuotientGroup.mk m : D.Sec) := by
    apply Additive.toMul.injective
    apply e.injective
    rfl
  change ((e (Additive.toMul (β (ρ γ w))) : ↥D.sec) : D.Amb) = D.act (θ γ) (m : D.Amb)
  rw [hint γ w m hm hw]
  rfl

end KerBot

section Herm

variable {F : Type} [Field F] [CharP F 2]

@[expose] def sig (a : ℕ) : F →+* F := iterateFrobenius F 2 a

theorem sig_apply (a : ℕ) (x : F) : sig a x = x ^ 2 ^ a := iterateFrobenius_def 2 a x

theorem frobPow_eq_map (a : ℕ) (X : Matrix (Fin 2) (Fin 2) F) :
    frobPow a X = (sig a).mapMatrix X := by
  ext i j
  simp [frobPow, sig_apply]

theorem sig_sig [Fintype F] {a : ℕ} (hF : Fintype.card F = 2 ^ (2 * a)) (x : F) :
    sig a (sig a x) = x := by
  rw [sig_apply, sig_apply, ← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]

@[expose] def hermA (a : ℕ) (F : Type) [Field F] [CharP F 2] :
    AddSubgroup (Matrix (Fin 2) (Fin 2) F) :=
  Subgroup.toAddSubgroup' (hermSub a (Fin 2) F)

theorem mem_hermA {a : ℕ} {X : Matrix (Fin 2) (Fin 2) F} :
    X ∈ hermA a F ↔ (frobPow a X)ᵀ = X := Iff.rfl

theorem hermA_apply {a : ℕ} {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA a F) (i j : Fin 2) :
    sig a (X j i) = X i j := by
  have h := congrFun (congrFun (mem_hermA.mp hX) i) j
  rwa [transpose_apply, frobPow_eq_map, RingHom.mapMatrix_apply, map_apply] at h

theorem hermA_00 {a : ℕ} (X : ↥(hermA a F)) : sig a ((X : Matrix (Fin 2) (Fin 2) F) 0 0) =
    (X : Matrix (Fin 2) (Fin 2) F) 0 0 :=
  hermA_apply X.2 0 0

theorem hermA_11 {a : ℕ} (X : ↥(hermA a F)) : sig a ((X : Matrix (Fin 2) (Fin 2) F) 1 1) =
    (X : Matrix (Fin 2) (Fin 2) F) 1 1 :=
  hermA_apply X.2 1 1

theorem hermA_10 {a : ℕ} (X : ↥(hermA a F)) : (X : Matrix (Fin 2) (Fin 2) F) 1 0 =
    sig a ((X : Matrix (Fin 2) (Fin 2) F) 0 1) :=
  (hermA_apply X.2 1 0).symm

theorem mem_hermA_of {a : ℕ} {X : Matrix (Fin 2) (Fin 2) F} (h : ∀ i j, sig a (X j i) = X i j) :
    X ∈ hermA a F := by
  rw [mem_hermA]
  ext i j
  rw [transpose_apply, frobPow_eq_map, RingHom.mapMatrix_apply, map_apply]
  exact h i j

theorem hermA_ext {a : ℕ} {X Y : ↥(hermA a F)}
    (h00 : (X : Matrix (Fin 2) (Fin 2) F) 0 0 = (Y : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = (Y : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = (Y : Matrix (Fin 2) (Fin 2) F) 1 1) : X = Y := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · change (X : Matrix (Fin 2) (Fin 2) F) 1 0 = (Y : Matrix (Fin 2) (Fin 2) F) 1 0
    rw [hermA_10, hermA_10, h01]
  · exact h11

theorem hermA_add_self {a : ℕ} (X : ↥(hermA a F)) : X + X = 0 := by
  apply Subtype.ext
  ext i j
  exact CharTwo.add_self_eq_zero _

variable (a : ℕ) (hσ : ∀ x : F, sig a (sig a x) = x)

include hσ in
theorem frobPow_frobPow (X : Matrix (Fin 2) (Fin 2) F) : frobPow a (frobPow a X) = X := by
  ext i j
  simp only [frobPow_eq_map, RingHom.mapMatrix_apply, map_apply, hσ]

theorem frobPow_mul (X Y : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (X * Y) = frobPow a X * frobPow a Y := by
  simp only [frobPow_eq_map, map_mul]

omit [CharP F 2] in
theorem frobPow_transpose (X : Matrix (Fin 2) (Fin 2) F) : frobPow a Xᵀ = (frobPow a X)ᵀ := by
  ext i j
  simp [frobPow]

include hσ in
theorem twist_mem {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA a F)
    (g : Matrix (Fin 2) (Fin 2) F) : g * X * (frobPow a g)ᵀ ∈ hermA a F := by
  rw [mem_hermA] at hX ⊢
  rw [frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow a hσ, transpose_mul,
    transpose_mul, transpose_transpose, hX, Matrix.mul_assoc]

@[expose] def hermAct : SL2 F →* AddMonoid.End ↥(hermA a F) where
  toFun g :=
    { toFun := fun X => ⟨(g : Matrix (Fin 2) (Fin 2) F) * X *
          (frobPow a (g : Matrix (Fin 2) (Fin 2) F))ᵀ, twist_mem a hσ X.2 _⟩
      map_zero' := by
        apply Subtype.ext
        change (g : Matrix (Fin 2) (Fin 2) F) * 0 * _ = 0
        rw [Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun X Y => by
        apply Subtype.ext
        change (g : Matrix (Fin 2) (Fin 2) F) * ((X : Matrix (Fin 2) (Fin 2) F) + Y) * _ =
          (g : Matrix (Fin 2) (Fin 2) F) * X * _ + (g : Matrix (Fin 2) (Fin 2) F) * Y * _
        rw [Matrix.mul_add, Matrix.add_mul] }
  map_one' := by
    refine AddMonoidHom.ext fun X => Subtype.ext ?_
    change (1 : Matrix (Fin 2) (Fin 2) F) * X * (frobPow a (1 : Matrix (Fin 2) (Fin 2) F))ᵀ = X
    rw [frobPow_eq_map, map_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  map_mul' g h := by
    refine AddMonoidHom.ext fun X => Subtype.ext ?_
    change ((g : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F)) * X *
      (frobPow a ((g : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F)))ᵀ =
      (g : Matrix (Fin 2) (Fin 2) F) * ((h : Matrix (Fin 2) (Fin 2) F) * X *
        (frobPow a (h : Matrix (Fin 2) (Fin 2) F))ᵀ) * (frobPow a (g : Matrix (Fin 2) (Fin 2) F))ᵀ
    rw [frobPow_mul, transpose_mul]
    simp only [Matrix.mul_assoc]

theorem hermAct_coe (g : SL2 F) (X : ↥(hermA a F)) :
    ((hermAct a hσ g X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow a (g : Matrix (Fin 2) (Fin 2) F))ᵀ :=
  rfl

omit [CharP F 2] in
theorem triple_apply (A X B : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (A * X * Bᵀ) i j = A i 0 * X 0 0 * B j 0 + A i 0 * X 0 1 * B j 1 +
      A i 1 * X 1 0 * B j 0 + A i 1 * X 1 1 * B j 1 := by
  simp only [mul_apply, Fin.sum_univ_two, transpose_apply]
  ring

theorem frobPow_uMat (t : F) :
    frobPow a ((uMat t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, sig a t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, uMat_coe, sig_apply]

theorem frobPow_tMat (c : F) (hc : c ≠ 0) :
    frobPow a ((tMat c hc : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![sig a c, 0; 0, sig a c⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, tMat_coe, sig_apply]

variable (X : ↥(hermA a F))

theorem hermAct_uMat_00 (t : F) :
    ((hermAct a hσ (uMat t) X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 + sig a t * (X : Matrix (Fin 2) (Fin 2) F) 0 1 +
        t * (X : Matrix (Fin 2) (Fin 2) F) 1 0 +
          t * sig a t * (X : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [hermAct_coe, triple_apply, frobPow_uMat, uMat_coe]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem hermAct_uMat_01 (t : F) :
    ((hermAct a hσ (uMat t) X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (X : Matrix (Fin 2) (Fin 2) F) 0 1 + t * (X : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [hermAct_coe, triple_apply, frobPow_uMat, uMat_coe]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem hermAct_uMat_11 (t : F) :
    ((hermAct a hσ (uMat t) X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (X : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [hermAct_coe, triple_apply, frobPow_uMat, uMat_coe]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem hermAct_tMat_00 (c : F) (hc : c ≠ 0) :
    ((hermAct a hσ (tMat c hc) X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      c * sig a c * (X : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  rw [hermAct_coe, triple_apply, frobPow_tMat, tMat_coe]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem hermAct_tMat_01 (c : F) (hc : c ≠ 0) :
    ((hermAct a hσ (tMat c hc) X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      c * sig a c⁻¹ * (X : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  rw [hermAct_coe, triple_apply, frobPow_tMat, tMat_coe]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

theorem hermAct_tMat_11 (c : F) (hc : c ≠ 0) :
    ((hermAct a hσ (tMat c hc) X : ↥(hermA a F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      c⁻¹ * sig a c⁻¹ * (X : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  rw [hermAct_coe, triple_apply, frobPow_tMat, tMat_coe]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  ring

end Herm

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def hermEquiv (a : ℕ) (F : Type) [Field F] [CharP F 2] :
    Additive ↥(hermSub a (Fin 2) F) ≃+ ↥(hermA a F) where
  toFun x := ⟨Multiplicative.toAdd ((Additive.toMul x : ↥(hermSub a (Fin 2) F)) :
    Multiplicative (Matrix (Fin 2) (Fin 2) F)), (Additive.toMul x).2⟩
  invFun X := Additive.ofMul ⟨Multiplicative.ofAdd (X : Matrix (Fin 2) (Fin 2) F), X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem BinaryOrthogonalFour.intertwiner {F : Type} [Field F] [CharP F 2] {a : ℕ}
    (hσ : ∀ x : F, sig a (sig a x) = x) {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.BinaryOrthogonalFour ρ F a) :
    ∃ (θ : Γ ≃* SL2 F) (β : W ≃+ ↥(hermA a F)), ∀ γ w, β (ρ γ w) = hermAct a hσ (θ γ) (β w) := by
  set e := specialLinearGroupEquivStatedSL 2 F
  have hcoe : ∀ y : ↥(StatedSL 2 F), ((e.symm y : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := fun y => by
    rw [← specialLinearGroupEquivStatedSL_coe 2 F (e.symm y), MulEquiv.apply_symm_apply]
  obtain ⟨θ₀, β₀, hw⟩ := h
  let θ₁ : Γ ≃* ↥(StatedSL 2 F) := θ₀
  refine ⟨θ₁.trans e.symm, (β₀.trans (secEquivSub _ rfl).toAdditive).trans (hermEquiv a F),
    fun γ w => Subtype.ext ?_⟩
  have h1 := congrArg Multiplicative.toAdd
    (Witness.sub (D := FFModel.twistTensor a (StatedSL 2 F)) (θ := θ₁) rfl hw γ w)
  refine h1.trans ?_
  rw [hermAct_coe, MulEquiv.trans_apply, hcoe]
  rfl

end CFSG.Quasithin.JonesParshall
