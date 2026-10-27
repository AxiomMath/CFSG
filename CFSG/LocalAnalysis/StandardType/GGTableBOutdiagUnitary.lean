module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped Matrix

namespace TableB

section Unitary

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

omit [Fintype ι] [DecidableEq ι] in
theorem transpose_map_smul (σ : K →+* K) (c : K) (M : Matrix ι ι K) :
    ((c • M).map σ)ᵀ = σ c • (M.map σ)ᵀ := by
  ext i j
  simp [Matrix.map_apply, map_mul]

@[expose] def unitGroup (σ : K →+* K) : Subgroup (GL ι K) where
  carrier := {A | ((A : Matrix ι ι K).map σ)ᵀ * (A : Matrix ι ι K) = 1}
  mul_mem' := by
    intro A B hA hB
    change ((A : Matrix ι ι K).map σ)ᵀ * (A : Matrix ι ι K) = 1 at hA
    change ((B : Matrix ι ι K).map σ)ᵀ * (B : Matrix ι ι K) = 1 at hB
    change (((A * B : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((A * B : GL ι K) : Matrix ι ι K) = 1
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((A : Matrix ι ι K).map σ)ᵀ, hA, Matrix.one_mul, hB]
  one_mem' := by
    change (((1 : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((1 : GL ι K) : Matrix ι ι K) = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one,
      Matrix.one_mul]
  inv_mem' := by
    intro A hA
    change ((A : Matrix ι ι K).map σ)ᵀ * (A : Matrix ι ι K) = 1 at hA
    change (((A⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1
    have hAA : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : ((A : Matrix ι ι K).map σ)ᵀ = ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
      calc ((A : Matrix ι ι K).map σ)ᵀ = ((A : Matrix ι ι K).map σ)ᵀ *
            ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
            rw [hAA, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
    calc (((A⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((A⁻¹ : GL ι K) : Matrix ι ι K) =
          (((A⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((A : Matrix ι ι K).map σ)ᵀ := by rw [h1]
      _ = (((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)).map σ)ᵀ := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
      _ = 1 := by
          rw [hAA, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem mem_unitGroup {σ : K →+* K} {A : GL ι K} :
    A ∈ unitGroup σ ↔ ((A : Matrix ι ι K).map σ)ᵀ * (A : Matrix ι ι K) = 1 :=
  Iff.rfl

theorem conj_unitary_of_similitude (σ : K →+* K) {P Q G : Matrix ι ι K} {μ : K}
    (hP : (P.map σ)ᵀ * P = μ • 1) (hPQ : P * Q = 1) (hG : (G.map σ)ᵀ * G = 1) :
    ((P * G * Q).map σ)ᵀ * (P * G * Q) = 1 := by
  have h1 : (P.map σ)ᵀ = μ • Q := by
    calc (P.map σ)ᵀ = (P.map σ)ᵀ * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = μ • Q := by rw [← Matrix.mul_assoc, hP, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (Q.map σ)ᵀ * (μ • Q) = 1 := by
    rw [← h1, ← Matrix.transpose_mul, ← Matrix.map_mul, hPQ,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  calc ((P * G * Q).map σ)ᵀ * (P * G * Q) =
        (Q.map σ)ᵀ * ((G.map σ)ᵀ * ((P.map σ)ᵀ * P) * G * Q) := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Q.map σ)ᵀ * (μ • Q) := by
        rw [hP, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hG, Matrix.smul_mul,
          Matrix.one_mul]
    _ = 1 := h2

@[expose] def IsSimilitude (σ : K →+* K) (A : GL ι K) : Prop :=
  ∃ μ : K, μ ≠ 0 ∧ ((A : Matrix ι ι K).map σ)ᵀ * (A : Matrix ι ι K) = μ • 1

theorem IsSimilitude.inv {σ : K →+* K} {A : GL ι K} (hA : IsSimilitude σ A) :
    IsSimilitude σ A⁻¹ := by
  obtain ⟨μ, hμ0, hA⟩ := hA
  refine ⟨μ⁻¹, inv_ne_zero hμ0, ?_⟩
  have hAA : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((A : Matrix ι ι K).map σ)ᵀ = μ • ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
    calc ((A : Matrix ι ι K).map σ)ᵀ = ((A : Matrix ι ι K).map σ)ᵀ *
          ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
          rw [hAA, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hA, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (((A⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ *
      (μ • ((A⁻¹ : GL ι K) : Matrix ι ι K)) = 1 := by
    rw [← h1, ← Matrix.transpose_mul, ← Matrix.map_mul, hAA,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  rw [Matrix.mul_smul] at h2
  rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

@[expose] def suGens (σ : K →+* K) : Set (GL ι K) :=
  {g | (g : Matrix ι ι K).det = 1 ∧ ((g : Matrix ι ι K).map σ)ᵀ * (g : Matrix ι ι K) = 1}

theorem conj_mem_suGens {σ : K →+* K} {A : GL ι K} (hA : IsSimilitude σ A) {g : GL ι K}
    (hg : g ∈ suGens σ) : A * g * A⁻¹ ∈ suGens σ := by
  obtain ⟨μ, -, hA⟩ := hA
  refine ⟨?_, ?_⟩
  · have hd : Matrix.GeneralLinearGroup.det g = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hg.1, Units.val_one])
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, hd, mul_one,
      mul_inv_cancel, Units.val_one]
  · simp only [Units.val_mul]
    exact conj_unitary_of_similitude σ hA (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      hg.2

theorem closure_suGens_le_comap {σ : K →+* K} {A : GL ι K} (hA : IsSimilitude σ A) :
    Subgroup.closure (suGens σ) ≤
      (Subgroup.closure (suGens (ι := ι) σ)).comap (MulAut.conj A).toMonoidHom := by
  rw [Subgroup.closure_le]
  intro g hg
  exact Subgroup.subset_closure (conj_mem_suGens hA hg)

theorem mem_normalizer_closure_suGens {σ : K →+* K} {A : GL ι K} (hA : IsSimilitude σ A) :
    A ∈ Subgroup.normalizer (Subgroup.closure (suGens (ι := ι) σ) : Set (GL ι K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => closure_suGens_le_comap hA hh, fun hh => ?_⟩
  have := closure_suGens_le_comap hA.inv hh
  simpa [mul_assoc] using this

theorem exists_pow_eq_of_pow_eq_one {G : Type*} [Group G] [IsCyclic G] [Finite G] {a b : ℕ}
    (hab : Nat.card G = a * b) (ha : 0 < a) {x : G} (hx : x ^ a = 1) : ∃ y : G, y ^ b = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  have hord : orderOf g = a * b := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hab
  have h1 : ((orderOf g : ℕ) : ℤ) ∣ m * a := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_natCast, hx]
  rw [hord, Nat.cast_mul, mul_comm m] at h1
  obtain ⟨j, hj⟩ := (mul_dvd_mul_iff_left (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0)).mp h1
  refine ⟨g ^ j, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, hj, mul_comm]

theorem exists_norm_eq [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) {μ : K}
    (hμ0 : μ ≠ 0) (hμq : μ ^ q = μ) : ∃ l : Kˣ, (l : K) ^ (q + 1) = μ := by
  have hcard : Nat.card Kˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_units, hK]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have h : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hx : (Units.mk0 μ hμ0) ^ (q - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have h : μ ^ (q - 1) * μ = 1 * μ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), hμq, one_mul]
    exact mul_right_cancel₀ hμ0 h
  obtain ⟨y, hy⟩ := exists_pow_eq_of_pow_eq_one hcard (by omega) hx
  exact ⟨y, by rw [← Units.val_pow_eq_pow_val, hy, Units.val_mk0]⟩

theorem coe_scalar_mul (u : Kˣ) (A : GL ι K) :
    ((Matrix.GeneralLinearGroup.scalar ι u * A : GL ι K) : Matrix ι ι K) =
      (u : K) • (A : Matrix ι ι K) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem ggOutdiagCyclic_unitary [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGOutdiagCyclic (LargeEvenProj (LargeEvenSUGroup ι K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup ι K (2 ^ n)))
        (LargeEvenGUSet ι K (2 ^ n))) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ x, σ x = x ^ 2 ^ n := iterateFrobenius_def 2 n
  have hm : ∀ M : Matrix ι ι K, M.map (· ^ 2 ^ n) = M.map σ := fun M => by
    ext i j
    simp [hσ]
  have hq : 2 ≤ 2 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hSU : LargeEvenSUGroup ι K (2 ^ n) = Subgroup.closure (suGens σ) := by
    unfold LargeEvenSUGroup suGens
    simp only [hm]
  have hGU : ∀ A ∈ LargeEvenGUSet ι K (2 ^ n), IsSimilitude σ A := by
    rintro A ⟨μ, hμ0, -, hA⟩
    exact ⟨μ, hμ0, by rw [← hm]; exact hA⟩
  have hN : LargeEvenGUSet ι K (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup ι K (2 ^ n) : Set (GL ι K)) := by
    intro A hA
    rw [hSU]
    exact mem_normalizer_closure_suGens (hGU A hA)
  set U := unitGroup (ι := ι) σ with hU
  obtain ⟨⟨d₀, A₀, hA₀U, hd₀⟩, hgen⟩ :=
    IsCyclic.exists_generator (α := U.map (Matrix.GeneralLinearGroup.det (n := ι)))
  have hA₀N : A₀ ∈ Subgroup.normalizer (LargeEvenSUGroup ι K (2 ^ n) : Set (GL ι K)) :=
    hN ⟨1, one_ne_zero, one_pow _, by rw [hm, one_smul]; exact hA₀U⟩
  refine ggOutdiagCyclic_of_decomp hN ⟨A₀, hA₀N⟩ ?_
  rintro A ⟨μ, hμ0, hμq, hA⟩
  rw [hm] at hA
  obtain ⟨l, hl⟩ := exists_norm_eq hq hK hμ0 hμq
  set A' := Matrix.GeneralLinearGroup.scalar ι l⁻¹ * A with hA'
  have hA'U : A' ∈ U := by
    rw [mem_unitGroup, hA', coe_scalar_mul, transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul,
      hA, smul_smul, smul_smul, hσ, ← hl]
    have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) = 1 := by
      have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
      calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) =
            (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ n * (((l⁻¹ : Kˣ) : K) * l) := by ring
        _ = 1 := by rw [hinv, one_pow, one_mul]
    rw [h0, one_smul]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (hgen ⟨Matrix.GeneralLinearGroup.det A', A', hA'U, rfl⟩)
  have hdet : Matrix.GeneralLinearGroup.det A' = Matrix.GeneralLinearGroup.det A₀ ^ k := by
    have h : d₀ ^ k = Matrix.GeneralLinearGroup.det A' := by
      simpa using congrArg Subtype.val hk
    rw [← h, hd₀]
  refine ⟨A' * A₀ ^ (-k), k, Matrix.GeneralLinearGroup.scalar ι l, ?_, ⟨l, rfl⟩, ?_⟩
  · rw [hSU]
    apply Subgroup.subset_closure
    refine ⟨?_, U.mul_mem hA'U (U.zpow_mem hA₀U _)⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_zpow, hdet, ← zpow_add,
      add_neg_cancel, zpow_zero, Units.val_one]
  · show A = A' * A₀ ^ (-k) * A₀ ^ k * Matrix.GeneralLinearGroup.scalar ι l
    rw [mul_assoc A', ← zpow_add, neg_add_cancel, zpow_zero, mul_one, hA', mul_assoc,
      (Subgroup.mem_center_iff.mp (scalar_mem_center (ι := ι) l)) A, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]


end Unitary

end TableB

theorem recipeUnitary_outdiag {d n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableB.ggOutdiagCyclic_unitary hK⟩

end CFSG.StandardType
