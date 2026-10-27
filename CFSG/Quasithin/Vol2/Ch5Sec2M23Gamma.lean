module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Local
public import CFSG.Quasithin.Vol2.Ch5Sec2M23GammaData
import CFSG.Quasithin.Background.F6ResPSigmaL2

public section

namespace CFSG.Quasithin.H13

open scoped Matrix

variable {K : Type} [Field K]

@[expose] def IsSemilin (f : Equiv.Perm (Fin 2 → K)) (A : GL (Fin 2) K) (σ : K ≃+* K) : Prop :=
  ∀ v, f v = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ (v i))

theorem ringEquiv_mulVec (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K) :
    (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ (fun i => σ (w i)) := by
  funext i
  exact RingHom.map_mulVec (σ : K →+* K) M w i

theorem IsSemilin.mul {f g : Equiv.Perm (Fin 2 → K)} {A B : GL (Fin 2) K} {σ τ : K ≃+* K}
    (hf : IsSemilin f A σ) (hg : IsSemilin g B τ) :
    IsSemilin (f * g) (A * Matrix.GeneralLinearGroup.map (σ : K →+* K) B) (τ.trans σ) := by
  intro v
  rw [Equiv.Perm.mul_apply, hg v, hf, ringEquiv_mulVec, Matrix.mulVec_mulVec]
  rfl

theorem IsSemilin.inv {f : Equiv.Perm (Fin 2 → K)} {A : GL (Fin 2) K} {σ : K ≃+* K}
    (hf : IsSemilin f A σ) :
    IsSemilin f⁻¹ (Matrix.GeneralLinearGroup.map (σ.symm : K →+* K) A⁻¹) σ.symm := by
  intro v
  rw [Equiv.Perm.inv_eq_iff_eq, hf]
  have h1 := ringEquiv_mulVec σ ((Matrix.GeneralLinearGroup.map (σ.symm : K →+* K) A⁻¹ :
    GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (fun i => σ.symm (v i))
  rw [h1]
  have h2 : ((Matrix.GeneralLinearGroup.map (σ.symm : K →+* K) A⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).map σ = ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    change σ (σ.symm (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j)) = _
    exact σ.apply_symm_apply _
  rw [h2]
  have h3 : (fun i => σ (σ.symm (v i))) = v := by
    funext i
    simp
  rw [h3, Matrix.mulVec_mulVec]
  simp

theorem isSemilin_one : IsSemilin (1 : Equiv.Perm (Fin 2 → K)) 1 (RingEquiv.refl K) := by
  intro v
  simp

theorem exists_isSemilin {f : Equiv.Perm (Fin 2 → K)} (hf : f ∈ GammaL2 K) :
    ∃ (A : GL (Fin 2) K) (σ : K ≃+* K), IsSemilin f A σ := by
  induction hf using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨A, hA⟩ | ⟨σ, hσ⟩
    · exact ⟨A, RingEquiv.refl K, fun v => by rw [hA]; rfl⟩
    · exact ⟨1, σ, fun v => by rw [hσ]; simp; rfl⟩
  | one => exact ⟨1, RingEquiv.refl K, isSemilin_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨A, σ, hA⟩ := hx
    obtain ⟨B, τ, hB⟩ := hy
    exact ⟨_, _, hA.mul hB⟩
  | inv x _ hx =>
    obtain ⟨A, σ, hA⟩ := hx
    exact ⟨_, _, hA.inv⟩

@[expose] def linPerm (A : GL (Fin 2) K) : Equiv.Perm (Fin 2 → K) :=
  ⟨fun v => (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v,
    fun v => ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v,
    fun v => by dsimp only; rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec],
    fun v => by dsimp only; rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

theorem linPerm_mem (A : GL (Fin 2) K) : linPerm A ∈ GammaL2 K :=
  Subgroup.subset_closure (Or.inl ⟨A, fun _ => rfl⟩)

theorem IsSemilin.apply_refl {f : Equiv.Perm (Fin 2 → K)} {A : GL (Fin 2) K}
    (h : IsSemilin f A (RingEquiv.refl K)) (w : Fin 2 → K) :
    f w = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w := by
  rw [h w]
  rfl

theorem IsSemilin.mul_apply_of_comp {f f' : Equiv.Perm (Fin 2 → K)} {A A' : GL (Fin 2) K}
    {σ σ' : K ≃+* K} (h : IsSemilin f A σ) (h' : IsSemilin f' A' σ') (hσ : ∀ x, σ (σ' x) = x)
    (w : Fin 2 → K) :
    (f * f') w =
      ((A : Matrix (Fin 2) (Fin 2) K) * (A' : Matrix (Fin 2) (Fin 2) K).map σ) *ᵥ w := by
  rw [Equiv.Perm.mul_apply, h' w, h, ringEquiv_mulVec, Matrix.mulVec_mulVec]
  congr 1
  funext i
  exact hσ (w i)

theorem pow_apply_of_mulVec {f : Equiv.Perm (Fin 2 → K)} {A : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ w, f w = A *ᵥ w) (n : ℕ) (w : Fin 2 → K) : (f ^ n) w = (A ^ n) *ᵥ w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, h, ih, Matrix.mulVec_mulVec, ← pow_succ]

theorem matrix_eq_of_mulVec {A B : Matrix (Fin 2) (Fin 2) K} (h : ∀ w, A *ᵥ w = B *ᵥ w) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem mulVec_scalar (c : K) (w : Fin 2 → K) : Matrix.scalar (Fin 2) c *ᵥ w = c • w := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]

section Four

variable [Finite K]

theorem ringEquiv_eq_refl_or_sq (hK : Nat.card K = 4) (σ : K ≃+* K) :
    σ = RingEquiv.refl K ∨ ∀ x, σ x = x ^ 2 := by
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr (CFSG.Quasithin.F6.PSigmaRes.ringAut_apply_eq_pow Nat.prime_two
      (by rw [hK]; norm_num) σ h)

theorem pow_four_eq_self (hK : Nat.card K = 4) (x : K) : x ^ 4 = x := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem pow_three_eq_one_of_ne_zero (hK : Nat.card K = 4) {x : K} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h := pow_four_eq_self hK x
  have : x * x ^ 3 = x * 1 := by rw [mul_one, ← pow_succ']; exact h
  exact mul_left_cancel₀ hx this

theorem sq_sq_eq_self (hK : Nat.card K = 4) (x : K) : (x ^ 2) ^ 2 = x := by
  rw [← pow_mul]
  exact pow_four_eq_self hK x

theorem eq_one_or_eq_or_eq_sq (hK : Nat.card K = 4) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {x : K}
    (hx : x ≠ 0) : x = 1 ∨ x = c ∨ x = c ^ 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc3 := pow_three_eq_one_of_ne_zero hK hc0
  have hc20 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  have hc21 : c ^ 2 ≠ 1 := fun h => hc1 (by
    have : c ^ 3 = c * c ^ 2 := by ring
    rw [hc3, h, mul_one] at this
    exact this.symm)
  have hc2c : c ^ 2 ≠ c := fun h => hc1 (by
    have : c * c = c * 1 := by rw [mul_one, ← sq]; exact h
    exact mul_left_cancel₀ hc0 this)
  have hcard : ({0, 1, c, c ^ 2} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hc2c.symm]
    · simp [hc1.symm, hc21.symm]
    · simp [zero_ne_one, hc0.symm, hc20.symm]
  have huniv : ({0, 1, c, c ^ 2} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, hK])
  have hmem : x ∈ ({0, 1, c, c ^ 2} : Finset K) := huniv ▸ Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h hx
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem ringEquivF4 (hK : Nat.card K = 4) : Nonempty (K ≃+* CFSG.Fischer.F4) := by
  have : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK,
    CFSG.Fischer.F4.card])⟩

omit [Finite K] in
theorem map_sq_mapMatrix {F : Type} [Field F] (κ : K ≃+* F) (A : Matrix (Fin 2) (Fin 2) K) :
    κ.mapMatrix (A.map (· ^ 2)) = (κ.mapMatrix A).map (· ^ 2) := by
  ext i j
  simp

omit [Finite K] in
theorem mapMatrix_scalar {F : Type} [Field F] (κ : K ≃+* F) (c : K) :
    κ.mapMatrix (Matrix.scalar (Fin 2) c) = Matrix.scalar (Fin 2) (κ c) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

theorem semilinear_involutions
    (hK : Nat.card K = 4) (P Q : Matrix (Fin 2) (Fin 2) K)
    (hP : P * P.map (· ^ 2) = 1) (hQ : Q * Q.map (· ^ 2) = 1) (hd : (P * Q.map (· ^ 2)).det = 1) :
    (P * Q.map (· ^ 2)) ^ 2 = 1 ∨ (P * Q.map (· ^ 2)) ^ 3 = 1 := by
  obtain ⟨κ⟩ := ringEquivF4 hK
  set κM := κ.mapMatrix (m := Fin 2)
  have hP' : κM P * (κM P).map (· ^ 2) = 1 := by
    rw [← map_sq_mapMatrix, ← map_mul, hP, map_one]
  have hQ' : κM Q * (κM Q).map (· ^ 2) = 1 := by
    rw [← map_sq_mapMatrix, ← map_mul, hQ, map_one]
  have hd' : (κM P * (κM Q).map (· ^ 2)).det = 1 := by
    rw [← map_sq_mapMatrix, ← map_mul]
    have h := RingEquiv.map_det κ (P * Q.map (· ^ 2))
    rw [hd, map_one] at h
    exact h.symm
  rcases gl2_semilinear_involutions _ _ hP' hQ' hd' with h | h
  · left
    apply κM.injective
    rw [map_pow, map_mul, map_sq_mapMatrix, h, map_one]
  · right
    apply κM.injective
    rw [map_pow, map_mul, map_sq_mapMatrix, h, map_one]

theorem cube_of_pow_nine
    (hK : Nat.card K = 4) (A : Matrix (Fin 2) (Fin 2) K) (hA : A ^ 9 = 1) :
    A ^ 3 = 1 := by
  obtain ⟨κ⟩ := ringEquivF4 hK
  set κM := κ.mapMatrix (m := Fin 2)
  have h := gl2_cube_of_pow_nine (κM A) (by rw [← map_pow, hA, map_one])
  apply κM.injective
  rw [map_pow, h, map_one]

omit [Finite K] in
theorem mapMatrix_symm_inv_smul_adjugate {F : Type} [Field F] (κ : K ≃+* F)
    (B : Matrix (Fin 2) (Fin 2) F) :
    κ.symm.mapMatrix (B.det⁻¹ • B.adjugate) =
      (κ.symm.mapMatrix B).det⁻¹ • (κ.symm.mapMatrix B).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, Matrix.det_fin_two]

theorem scalar_of_conj_cube
    (hK : Nat.card K = 4) (A : Matrix (Fin 2) (Fin 2) K) (hA : A ^ 3 = 1)
    (hc : ∀ B : Matrix (Fin 2) (Fin 2) K, B.det ≠ 0 →
      (A * (B * A * (B.det⁻¹ • B.adjugate))) ^ 3 = 1) :
    ∃ c : K, A = Matrix.scalar (Fin 2) c := by
  obtain ⟨κ⟩ := ringEquivF4 hK
  set κM := κ.mapMatrix (m := Fin 2)
  obtain ⟨c, hc'⟩ := gl2_scalar_of_conj_cube (κM A) (by rw [← map_pow, hA, map_one])
    (fun B hB => by
      have hdet : (κ.symm.mapMatrix B).det ≠ 0 := by
        rw [← RingEquiv.map_det]
        exact (map_ne_zero κ.symm).mpr hB
      have h := hc _ hdet
      rw [← mapMatrix_symm_inv_smul_adjugate] at h
      have e : κM.symm = κ.symm.mapMatrix := rfl
      rw [← e] at h
      have := congrArg κM h
      rwa [map_pow, map_mul, map_mul, map_mul, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply, map_one] at this)
  refine ⟨κ.symm c, ?_⟩
  apply κM.injective
  rw [hc', mapMatrix_scalar, RingEquiv.apply_symm_apply]

end Four

section FourElements

variable [Finite K]

theorem trans_self_eq_refl (hK : Nat.card K = 4) (σ : K ≃+* K) :
    σ.trans σ = RingEquiv.refl K := by
  rcases ringEquiv_eq_refl_or_sq hK σ with h | h
  · subst h
    ext x
    rfl
  · ext x
    rw [RingEquiv.trans_apply, h, h, sq_sq_eq_self hK, RingEquiv.refl_apply]

theorem exists_isSemilin_mul_self (hK : Nat.card K = 4) {f : Equiv.Perm (Fin 2 → K)}
    (hf : f ∈ GammaL2 K) : ∃ B : GL (Fin 2) K, IsSemilin (f * f) B (RingEquiv.refl K) := by
  obtain ⟨A, σ, hA⟩ := exists_isSemilin hf
  have h := hA.mul hA
  rw [trans_self_eq_refl hK] at h
  exact ⟨_, h⟩

theorem exists_mulVec_of_pow_odd (hK : Nat.card K = 4) {f : Equiv.Perm (Fin 2 → K)}
    (hf : f ∈ GammaL2 K) {m : ℕ} (hm : f ^ (2 * m + 1) = 1) :
    ∃ B : GL (Fin 2) K, ∀ w, f w = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ w := by
  have e : f ^ (m + 1) * f ^ (m + 1) = f := by
    rw [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hm, one_mul]
  obtain ⟨B, hB⟩ := exists_isSemilin_mul_self hK ((GammaL2 K).pow_mem hf (m + 1))
  rw [e] at hB
  exact ⟨B, hB.apply_refl⟩

theorem cube_of_pow_three_pow
    (hK : Nat.card K = 4) {A : Matrix (Fin 2) (Fin 2) K} :
    ∀ k : ℕ, A ^ (3 ^ k) = 1 → A ^ 3 = 1
  | 0, h => by rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | 1, h => by rwa [pow_one] at h
  | k + 2, h => by
    refine cube_of_pow_three_pow hK (k + 1) ?_
    have h9 : (A ^ (3 ^ k)) ^ 9 = 1 := by
      rw [← pow_mul, show 3 ^ k * 9 = 3 ^ (k + 2) by ring]
      exact h
    rw [show 3 ^ (k + 1) = 3 ^ k * 3 by ring, pow_mul]
    exact cube_of_pow_nine hK _ h9

theorem exists_smul_of_mem_normal
    (hK : Nat.card K = 4) {Y : Subgroup ↥(GammaL2 K)}
    (hY : Y.Normal) (h3 : ∀ y ∈ Y, ∃ k : ℕ, y ^ (3 ^ k) = 1) {y : ↥(GammaL2 K)} (hy : y ∈ Y) :
    ∃ c : K, c ≠ 0 ∧ ∀ w, (y : Equiv.Perm (Fin 2 → K)) w = c • w := by
  have hlin : ∀ z ∈ Y, ∃ A : Matrix (Fin 2) (Fin 2) K, A ^ 3 = 1 ∧
      ∀ w, (z : Equiv.Perm (Fin 2 → K)) w = A *ᵥ w := by
    intro z hz
    obtain ⟨k, hk⟩ := h3 z hz
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have hk' : (z : Equiv.Perm (Fin 2 → K)) ^ (2 * m + 1) = 1 := by
      rw [← hm, ← Subgroup.coe_pow, hk, Subgroup.coe_one]
    obtain ⟨B, hB⟩ := exists_mulVec_of_pow_odd hK z.2 hk'
    refine ⟨B, cube_of_pow_three_pow hK k ?_, hB⟩
    apply matrix_eq_of_mulVec
    intro w
    rw [← pow_apply_of_mulVec hB, ← Subgroup.coe_pow, hk, Subgroup.coe_one, Matrix.one_mulVec]
    rfl
  obtain ⟨A, hA3, hAy⟩ := hlin y hy
  obtain ⟨c, hc⟩ := scalar_of_conj_cube hK A hA3 (fun B hB => by
    set B' := B.det⁻¹ • B.adjugate with hB'
    have h1 : B * B' = 1 := by
      rw [hB', Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hB, one_smul]
    have h2 : B' * B = 1 := by
      rw [hB', Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ hB, one_smul]
    set U : GL (Fin 2) K := ⟨B, B', h1, h2⟩
    set ℓ : ↥(GammaL2 K) := ⟨linPerm U, linPerm_mem U⟩
    have hz : y * (ℓ * y * ℓ⁻¹) ∈ Y := Y.mul_mem hy (hY.conj_mem y hy ℓ)
    obtain ⟨Az, hAz3, hAzv⟩ := hlin _ hz
    have hEq : Az = A * (B * A * B') := by
      apply matrix_eq_of_mulVec
      intro w
      have e1 : ((y * (ℓ * y * ℓ⁻¹) : ↥(GammaL2 K)) : Equiv.Perm (Fin 2 → K)) w =
          (y : Equiv.Perm (Fin 2 → K)) (B *ᵥ ((y : Equiv.Perm (Fin 2 → K)) (B' *ᵥ w))) := rfl
      rw [← hAzv, e1, hAy, hAy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc]
    rw [← hEq]
    exact hAz3)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : (Matrix.scalar (Fin 2) (0 : K)) ^ 3 = 1 := hc ▸ hA3
    rw [map_zero, zero_pow (by norm_num)] at h0
    exact zero_ne_one h0
  refine ⟨c, hc0, fun w => ?_⟩
  rw [hAy, hc, mulVec_scalar]

theorem card_le_three_of_normal
    (hK : Nat.card K = 4) {Y : Subgroup ↥(GammaL2 K)}
    (hY : Y.Normal) (h3 : ∀ y ∈ Y, ∃ k : ℕ, y ^ (3 ^ k) = 1) : Nat.card Y ≤ 3 := by
  have hf : ∀ y : Y, ∃ c : K, c ≠ 0 ∧
      ∀ w, ((y : ↥(GammaL2 K)) : Equiv.Perm (Fin 2 → K)) w = c • w :=
    fun y => exists_smul_of_mem_normal hK hY h3 y.2
  choose c hc0 hcw using hf
  have hinj : Function.Injective (fun y : Y => (⟨c y, hc0 y⟩ : {a : K // a ≠ 0})) := by
    intro y1 y2 h
    have hc : c y1 = c y2 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro w
    rw [hcw, hcw, hc]
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card {a : K // a ≠ 0} = 3 := by
    rw [← Nat.card_congr unitsEquivNeZero, Nat.card_units, hK]
  omega

theorem exists_orderOf_mul_le_three
    (hK : Nat.card K = 4) {g u v : ↥(GammaL2 K)}
    (hg3 : orderOf g = 3) (hn : ∀ h, h * g * h⁻¹ ∈ Subgroup.zpowers g) (huu : u * u = 1)
    (hvv : v * v = 1) (hug : u * g * u⁻¹ = g⁻¹) (hvg : v * g * v⁻¹ = g⁻¹) :
    ∃ j : ℕ, orderOf (g ^ j * u * v) ≤ 3 := by
  have hg3' : g ^ 3 = 1 := hg3 ▸ pow_orderOf_eq_one g
  have hYn : (Subgroup.zpowers g).Normal := ⟨fun n hn' h => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn'
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hn h) k⟩
  have hY3 : ∀ y ∈ Subgroup.zpowers g, ∃ k : ℕ, y ^ (3 ^ k) = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3', one_zpow]
  obtain ⟨c, hc0, hgw⟩ := exists_smul_of_mem_normal hK hYn hY3 (Subgroup.mem_zpowers g)
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hg1 : g = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro w
      rw [hgw, one_smul]
      rfl
    rw [hg1, orderOf_one] at hg3
    norm_num at hg3
  have hc3 : c ^ 3 = 1 := pow_three_eq_one_of_ne_zero hK hc0
  have hgj : ∀ j : ℕ, ∀ w,
      ((g ^ j : ↥(GammaL2 K)) : Equiv.Perm (Fin 2 → K)) w = c ^ j • w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ, Subgroup.coe_mul, Equiv.Perm.mul_apply, hgw, ih, smul_smul, ← pow_succ]
  have hsemi : ∀ s : ↥(GammaL2 K), s * s = 1 → s * g * s⁻¹ = g⁻¹ →
      ∃ (A : GL (Fin 2) K) (σ : K ≃+* K), IsSemilin s A σ ∧ (∀ x, σ x = x ^ 2) ∧
        (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K).map (· ^ 2) = 1 := by
    intro s hss hsg
    obtain ⟨A, σ, hA⟩ := exists_isSemilin s.2
    have hσ : ∀ x, σ x = x ^ 2 := by
      rcases ringEquiv_eq_refl_or_sq hK σ with h | h
      · exfalso
        subst h
        have hcomm : s * g = g * s := by
          apply Subtype.ext
          apply Equiv.ext
          intro w
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgw,
            hA.apply_refl, hA.apply_refl, hgw, Matrix.mulVec_smul]
        have hgg : g = g⁻¹ := by
          rw [← hsg, hcomm, mul_inv_cancel_right]
        have h2 : g ^ 2 = 1 := by
          rw [sq]
          calc g * g = g * g⁻¹ := congrArg (g * ·) hgg
            _ = 1 := mul_inv_cancel g
        have h32 := orderOf_dvd_of_pow_eq_one h2
        rw [hg3] at h32
        norm_num at h32
      · exact h
    refine ⟨A, σ, hA, hσ, ?_⟩
    have hss' : ∀ w, ((s * s : ↥(GammaL2 K)) : Equiv.Perm (Fin 2 → K)) w =
        ((A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K).map σ) *ᵥ w :=
      hA.mul_apply_of_comp hA (fun x => by rw [hσ, hσ, sq_sq_eq_self hK])
    have hmap : (A : Matrix (Fin 2) (Fin 2) K).map σ =
        (A : Matrix (Fin 2) (Fin 2) K).map (· ^ 2) := by
      ext i j
      exact hσ _
    rw [← hmap]
    apply matrix_eq_of_mulVec
    intro w
    rw [← hss', hss, Matrix.one_mulVec]
    rfl
  obtain ⟨Au, σu, hAu, hσu, hAu2⟩ := hsemi u huu hug
  obtain ⟨Av, σv, hAv, hσv, hAv2⟩ := hsemi v hvv hvg
  set P0 := (Au : Matrix (Fin 2) (Fin 2) K) with hP0
  set Q := (Av : Matrix (Fin 2) (Fin 2) K) with hQ
  have huv : ∀ w, ((u * v : ↥(GammaL2 K)) : Equiv.Perm (Fin 2 → K)) w =
      (P0 * Q.map (· ^ 2)) *ᵥ w := by
    intro w
    have h := hAu.mul_apply_of_comp hAv (fun x => by rw [hσu, hσv, sq_sq_eq_self hK]) w
    have hmap : Q.map σu = Q.map (· ^ 2) := by
      ext i j
      exact hσu _
    rw [← hmap]
    exact h
  have hdetP0 : P0.det ≠ 0 := fun h0 => by
    have h1 := congrArg Matrix.det hAu2
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetQ : (Q.map (· ^ 2)).det ≠ 0 := fun h0 => by
    have h1 := congrArg Matrix.det hAv2
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  set d := P0.det * (Q.map (· ^ 2)).det with hd
  have hd0 : d ≠ 0 := mul_ne_zero hdetP0 hdetQ
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (c ^ j) ^ 2 * d = 1 := by
    rcases eq_one_or_eq_or_eq_sq hK hc0 hc1 hd0 with h | h | h
    · exact ⟨0, by rw [h]; ring⟩
    · refine ⟨1, ?_⟩
      rw [h]
      calc (c ^ 1) ^ 2 * c = c ^ 3 := by ring
        _ = 1 := hc3
    · refine ⟨2, ?_⟩
      rw [h]
      calc (c ^ 2) ^ 2 * c ^ 2 = (c ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hc3, one_pow]
  set P := c ^ j • P0 with hP
  have hPP : P * P.map (· ^ 2) = 1 := by
    have hmap : P.map (· ^ 2) = (c ^ j) ^ 2 • P0.map (· ^ 2) := by
      ext i k
      simp [hP, mul_pow]
    rw [hmap, hP, Matrix.smul_mul, Matrix.mul_smul, hAu2, smul_smul,
      show c ^ j * (c ^ j) ^ 2 = (c ^ 3) ^ j by ring, hc3, one_pow, one_smul]
  have hdetN : (P * Q.map (· ^ 2)).det = 1 := by
    rw [Matrix.det_mul, hP, Matrix.det_smul, Fintype.card_fin, mul_assoc, ← hd, hj]
  have hN : ∀ w, ((g ^ j * u * v : ↥(GammaL2 K)) : Equiv.Perm (Fin 2 → K)) w =
      (P * Q.map (· ^ 2)) *ᵥ w := by
    intro w
    rw [mul_assoc, Subgroup.coe_mul, Equiv.Perm.mul_apply, huv, hgj, hP, Matrix.smul_mul,
      Matrix.smul_mulVec]
  have hpow : ∀ m : ℕ, (P * Q.map (· ^ 2)) ^ m = 1 → (g ^ j * u * v) ^ m = 1 := by
    intro m hm
    apply Subtype.ext
    apply Equiv.ext
    intro w
    rw [Subgroup.coe_pow, pow_apply_of_mulVec hN, hm, Matrix.one_mulVec]
    rfl
  refine ⟨j, ?_⟩
  rcases semilinear_involutions hK P Q hPP hAv2 hdetN with h2 | h3
  · exact (orderOf_le_of_pow_eq_one (by norm_num) (hpow 2 h2)).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) (hpow 3 h3)

theorem exists_orderOf_mul_le_three_of_mulEquiv
    {H : Type*} [Group H] (Ψ : H ≃* ↥(GammaL2 K))
    (hK : Nat.card K = 4) {x s t : H} (hx3 : orderOf x = 3)
    (hn : ∀ h : H, h * x * h⁻¹ ∈ Subgroup.zpowers x) (hss : s * s = 1) (htt : t * t = 1)
    (hsx : s * x * s⁻¹ = x⁻¹) (htx : t * x * t⁻¹ = x⁻¹) :
    ∃ j : ℕ, orderOf (x ^ j * s * t) ≤ 3 := by
  have hmap : ∀ a b : H, a * b * a⁻¹ = b⁻¹ → Ψ a * Ψ b * (Ψ a)⁻¹ = (Ψ b)⁻¹ := by
    intro a b hab
    have := congrArg Ψ hab
    simpa [map_mul, map_inv] using this
  obtain ⟨j, hj⟩ := exists_orderOf_mul_le_three hK (g := Ψ x) (u := Ψ s) (v := Ψ t)
    (by rw [MulEquiv.orderOf_eq, hx3])
    (fun h => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hn (Ψ.symm h))
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Ψ hk
      simpa [map_mul, map_inv, map_zpow] using this)
    (by rw [← map_mul, hss, map_one]) (by rw [← map_mul, htt, map_one]) (hmap s x hsx)
    (hmap t x htx)
  refine ⟨j, ?_⟩
  rwa [← map_pow, ← map_mul, ← map_mul, MulEquiv.orderOf_eq] at hj

theorem card_le_three_of_mulEquiv
    {H : Type*} [Group H] (Ψ : H ≃* ↥(GammaL2 K))
    (hK : Nat.card K = 4) {Y : Subgroup H} (hY : Y.Normal)
    (h3 : ∀ y ∈ Y, ∃ k : ℕ, y ^ (3 ^ k) = 1) : Nat.card Y ≤ 3 := by
  have h := card_le_three_of_normal hK (Y := Y.map Ψ.toMonoidHom) (hY.map _ Ψ.surjective) (by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := h3 y hy
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩)
  rwa [Subgroup.card_map_of_injective Ψ.injective] at h

end FourElements

end CFSG.Quasithin.H13
