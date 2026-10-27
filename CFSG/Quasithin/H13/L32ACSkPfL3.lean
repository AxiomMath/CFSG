module

public import CFSG.Quasithin.H13.L32ACSkPfL2
public import CFSG.Quasithin.H13.KGFact22TorL3
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag renaming conjAut → lConj, fieldAut → lField,
  dualAut → lDual
open Matrix

section L3

variable {K : Type} [Field K]

local notation "SL₃" => SpecialLinearGroup (Fin 3) K

theorem proj_diag3_mem_iff (x y z : K) (h : x * y * z = 1) :
    proj 3 K (KG22.diag3 x y z h) ∈ projUnitriangular 3 K → x = y ∧ y = z := by
  rintro ⟨u, hu, he⟩
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp he)
  have h1 : ((KG22.diag3 x y z h : SL₃) : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hd : ∀ i, ((KG22.diag3 x y z h : SL₃) : Matrix (Fin 3) (Fin 3) K) i i = c := by
    intro i
    rw [h1, scalar_apply, mul_diagonal, hu.2 i, one_mul]
  have h0 := hd 0
  have h1' := hd 1
  have h2 := hd 2
  simp only [KG22.coe_diag3, diagonal_apply_eq] at h0 h1' h2
  simp at h0 h1' h2
  exact ⟨h0.trans h1'.symm, h1'.trans h2.symm⟩

theorem psl3_comm_mem [Finite K] [CharP K 2] :
    ∀ a ∈ Subgroup.normalizer ((projUnitriangular 3 K : Subgroup _) : Set (projectiveSL 3 K)),
      ∀ b ∈ Subgroup.normalizer ((projUnitriangular 3 K : Subgroup _) : Set (projectiveSL 3 K)),
        a * b * a⁻¹ * b⁻¹ ∈ projUnitriangular 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha b hb
  rw [normalizer_projUnitriangular 2] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨_, comm_mem_unitriangular ha' hb', by simp only [map_mul, map_inv]⟩

theorem map_fieldAut_projUnitriangular [Finite K] (σ : K ≃+* K) :
    (projUnitriangular 3 K).map (lField 3 K σ).toMonoidHom = projUnitriangular 3 K := by
  refine map_eq_of_forall_mem ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨SpecialLinearGroup.map σ.toRingHom u, ⟨fun i j hij => ?_, fun i => ?_⟩,
    (fieldAut_proj σ u).symm⟩
  · change σ ((u : Matrix (Fin 3) (Fin 3) K) i j) = 0
    rw [hu.1 i j hij, map_zero]
  · change σ ((u : Matrix (Fin 3) (Fin 3) K) i i) = 1
    rw [hu.2 i, map_one]

@[expose] noncomputable def l3T (K : Type) [Field K] : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp KG22.tY

@[expose] noncomputable def l3T' (K : Type) [Field K] : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp KG22.tY'

theorem fieldAut_l3T (σ : K ≃+* K) (a : Kˣ) :
    lField 3 K σ (l3T K a) = l3T K (Units.map σ.toRingHom.toMonoidHom a) := by
  change lField 3 K σ (proj 3 K (KG22.tY a)) = proj 3 K (KG22.tY _)
  rw [fieldAut_proj]
  congr 1
  ext i j
  change σ ((KG22.tY a : SL₃) i j) = (KG22.tY _ : SL₃) i j
  rw [KG22.coe_tY, KG22.coe_tY]
  fin_cases i <;> fin_cases j <;> simp [Units.val_inv_eq_inv_val, map_inv₀]

theorem l3T_mem_iff (a : Kˣ) : l3T K a ∈ projUnitriangular 3 K → a = 1 := by
  intro h
  have h1 := proj_diag3_mem_iff (a : K) 1 ((a⁻¹ : Kˣ) : K) (by simp) h
  exact Units.ext h1.1

theorem l3T'_mem_iff (b : Kˣ) : l3T' K b ∈ projUnitriangular 3 K ↔ b ^ 3 = 1 := by
  constructor
  · intro h
    have h1 := (proj_diag3_mem_iff (b : K) (((b⁻¹ : Kˣ) : K) ^ 2) (b : K) (by
      rw [Units.val_inv_eq_inv_val]
      field_simp) h).1
    have h2 : b = b⁻¹ ^ 2 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
    calc b ^ 3 = b ^ 2 * b := by group
      _ = b ^ 2 * b⁻¹ ^ 2 := by rw [← h2]
      _ = 1 := by group
  · intro h
    have hb' : b⁻¹ ^ 2 = b := by
      calc b⁻¹ ^ 2 = b⁻¹ ^ 2 * b ^ 3 := by rw [h, mul_one]
        _ = b := by group
    have hb : (((b⁻¹ : Kˣ) : K)) ^ 2 = b := by
      rw [← Units.val_pow_eq_pow_val, hb']
    refine ⟨1, one_mem _, ?_⟩
    change proj 3 K 1 = proj 3 K (KG22.tY' b)
    rw [proj_eq_proj_iff, inv_one, one_mul, mem_scalars]
    refine ⟨b, h, ?_⟩
    rw [KG22.coe_tY', hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalar_apply]

theorem l3T_range_le [Finite K] [CharP K 2] :
    (l3T K).range ≤ Subgroup.normalizer ((projUnitriangular 3 K : Subgroup _) :
      Set (projectiveSL 3 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨a, rfl⟩
  rw [normalizer_projUnitriangular 2]
  exact ⟨_, KG22.tY_mem_upperTriangular a, rfl⟩

theorem l3T'_range_le [Finite K] [CharP K 2] :
    (l3T' K).range ≤ Subgroup.normalizer ((projUnitriangular 3 K : Subgroup _) :
      Set (projectiveSL 3 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨b, rfl⟩
  rw [normalizer_projUnitriangular 2]
  exact ⟨_, KG22.tY'_mem_upperTriangular b, rfl⟩

section Graph

variable [CharP K 2]

@[expose] noncomputable def gammaL3 (K : Type) [Field K] [CharP K 2] :
    MulAut (projectiveSL 3 K) :=
  MulAut.conj (proj 3 K KG22.w3) * lDual 3 K

theorem gammaL3_proj (g : SL₃) :
    gammaL3 K (proj 3 K g) = proj 3 K (KG22.w3 * (g⁻¹).transpose * KG22.w3⁻¹) := by
  rw [gammaL3, MulAut.mul_apply, dualAut_proj, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem w3_conj_apply (M : SL₃) (i j : Fin 3) :
    ((KG22.w3 * M * KG22.w3⁻¹ : SL₃) : Matrix (Fin 3) (Fin 3) K) i j =
      (M : Matrix (Fin 3) (Fin 3) K) (Fin.rev i) (Fin.rev j) := by
  rw [KG22.w3_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    KG22.coe_w3]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem w3_conj_inv_transpose_mem {u : SL₃} (hu : u ∈ unitriangular 3 K) :
    KG22.w3 * (u⁻¹).transpose * KG22.w3⁻¹ ∈ unitriangular 3 K := by
  have hui := inv_mem hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [w3_conj_apply, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
    exact hui.1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [w3_conj_apply, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
    exact hui.2 _

theorem map_gammaL3_projUnitriangular [Finite K] :
    (projUnitriangular 3 K).map (gammaL3 K).toMonoidHom = projUnitriangular 3 K := by
  refine map_eq_of_forall_mem ?_
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨_, w3_conj_inv_transpose_mem hu, (gammaL3_proj u).symm⟩

omit [CharP K 2] in
theorem transpose_tY (a : Kˣ) : (KG22.tY a).transpose = KG22.tY a :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_transpose, KG22.coe_tY, diagonal_transpose])

omit [CharP K 2] in
theorem transpose_tY' (b : Kˣ) : (KG22.tY' b).transpose = KG22.tY' b :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_transpose, KG22.coe_tY', diagonal_transpose])

theorem gammaL3_l3T (a : Kˣ) : gammaL3 K (l3T K a) = l3T K a := by
  change gammaL3 K (proj 3 K (KG22.tY a)) = proj 3 K (KG22.tY a)
  rw [gammaL3_proj, ← map_inv, transpose_tY, KG22.w3_conj_tY, ← map_inv KG22.tY, inv_inv]

theorem gammaL3_l3T' (b : Kˣ) : gammaL3 K (l3T' K b) = l3T' K b⁻¹ := by
  change gammaL3 K (proj 3 K (KG22.tY' b)) = proj 3 K (KG22.tY' b⁻¹)
  rw [gammaL3_proj, ← map_inv, transpose_tY', KG22.w3_conj_tY']

theorem fieldAut_proj_w3 (σ : K ≃+* K) :
    lField 3 K σ (proj 3 K KG22.w3) = proj 3 K KG22.w3 := by
  rw [fieldAut_proj]
  congr 1
  ext i j
  change σ ((KG22.w3 : SL₃) i j) = (KG22.w3 : SL₃) i j
  rw [KG22.coe_w3]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_conjAut_mul_std [Finite K] (α : MulAut (projectiveSL 3 K)) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      α = lConj 3 K A * (lField 3 K σ * gammaL3 K ^ ε) := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (n := 3) (K := K) (by norm_num)).2 α
  interval_cases ε
  · exact ⟨A, σ, 0, zero_le_one, by rw [pow_zero, pow_zero, mul_one, mul_one]⟩
  · refine ⟨A * (SpecialLinearGroup.toGL KG22.w3)⁻¹, σ, 1, le_rfl, ?_⟩
    have hc : lField 3 K σ * MulAut.conj (proj 3 K KG22.w3) =
        MulAut.conj (proj 3 K KG22.w3) * lField 3 K σ := by
      have h := SkPf.mul_conj_mul_inv (lField 3 K σ) (proj 3 K KG22.w3)
      rw [fieldAut_proj_w3] at h
      calc lField 3 K σ * MulAut.conj (proj 3 K KG22.w3) =
          lField 3 K σ * MulAut.conj (proj 3 K KG22.w3) * (lField 3 K σ)⁻¹ *
            lField 3 K σ := by group
        _ = MulAut.conj (proj 3 K KG22.w3) * lField 3 K σ := by rw [h]
    rw [pow_one, pow_one, gammaL3, map_mul, map_inv,
      ← CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 K KG22.w3,
      ← mul_assoc (lField 3 K σ), hc]
    group

end Graph

section Linear

@[expose] noncomputable def dGL3 (d : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(d : K), 1, 1], diagonal ![((d⁻¹ : Kˣ) : K), 1, 1], by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp, by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

theorem coe_dGL3 (d : Kˣ) :
    ((dGL3 d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(d : K), 1, 1] :=
  rfl

theorem coe_dGL3_inv (d : Kˣ) :
    (((dGL3 d)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![((d⁻¹ : Kˣ) : K), 1, 1] :=
  rfl

theorem dGL3_conj_apply (d : Kˣ) (M : SL₃) (i j : Fin 3) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K (dGL3 d) M :
        SL₃) : Matrix (Fin 3) (Fin 3) K) i j =
      ![(d : K), 1, 1] i * (M : Matrix (Fin 3) (Fin 3) K) i j *
        ![((d⁻¹ : Kˣ) : K), 1, 1] j := by
  rw [coe_slConjugation, coe_dGL3, coe_dGL3_inv, mul_diagonal, diagonal_mul]

theorem dGL3_mem_unitriangular (d : Kˣ) {u : SL₃} (hu : u ∈ unitriangular 3 K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K (dGL3 d) u ∈
      unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [dGL3_conj_apply, hu.1 i j hij, mul_zero, zero_mul]
  · rw [dGL3_conj_apply, hu.2 i, mul_one]
    fin_cases i <;> simp

theorem map_lConj_dGL3 [Finite K] (d : Kˣ) :
    (projUnitriangular 3 K).map (lConj 3 K (dGL3 d)).toMonoidHom = projUnitriangular 3 K :=
  map_eq_of_forall_mem (by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, dGL3_mem_unitriangular d hu, (conjAut_proj _ u).symm⟩)

theorem lConj_dGL3_cent [Finite K] [CharP K 2] (d : Kˣ) :
    ∀ b ∈ Subgroup.normalizer ((projUnitriangular 3 K : Subgroup _) : Set (projectiveSL 3 K)),
      lConj 3 K (dGL3 d) b * b⁻¹ ∈ projUnitriangular 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro b hb
  rw [normalizer_projUnitriangular 2] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  rw [conjAut_proj, ← map_inv, ← map_mul]
  set X := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K (dGL3 d) b'
  have hX : X ∈ upperTriangular 3 K := fun i j hij => by
    rw [dGL3_conj_apply, hb' i j hij, mul_zero, zero_mul]
  have hb'' := mem_upperTriangular_iff_isUpperTriangular.mp hb'
  refine ⟨X * b'⁻¹, ⟨mul_mem hX (inv_mem hb'), fun i => ?_⟩, rfl⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular
    (mem_upperTriangular_iff_isUpperTriangular.mp hX) (coe_inv_isUpperTriangular hb''),
    dGL3_conj_apply]
  have h1 := coe_inv_apply_self_of_isUpperTriangular hb'' i
  have hd : (d : K) ≠ 0 := d.ne_zero
  fin_cases i <;> simp at h1 ⊢
  · field_simp
    linear_combination h1
  · exact h1
  · exact h1

theorem lConj_cent [Finite K] [CharP K 2] (A : GL (Fin 3) K)
    (hA : (projUnitriangular 3 K).map (lConj 3 K A).toMonoidHom = projUnitriangular 3 K) :
    ∀ b ∈ Subgroup.normalizer ((projUnitriangular 3 K : Subgroup _) : Set (projectiveSL 3 K)),
      lConj 3 K A b * b⁻¹ ∈ projUnitriangular 3 K := by
  set d := Matrix.GeneralLinearGroup.det A
  have hdet : ((A * (dGL3 d)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, det_mul, coe_dGL3_inv, det_diagonal, Fin.prod_univ_three,
      ← Matrix.GeneralLinearGroup.val_det_apply]
    have h2 : (![((d⁻¹ : Kˣ) : K), 1, 1] : Fin 3 → K) 1 = 1 := rfl
    have h3 : (![((d⁻¹ : Kˣ) : K), 1, 1] : Fin 3 → K) 2 = 1 := rfl
    have h0 : (![((d⁻¹ : Kˣ) : K), 1, 1] : Fin 3 → K) 0 = ((d⁻¹ : Kˣ) : K) := rfl
    rw [h0, h2, h3, mul_one, mul_one, Units.mul_inv]
  set g : SL₃ := ⟨_, hdet⟩
  have hgA : lConj 3 K A = MulAut.conj (proj 3 K g) * lConj 3 K (dGL3 d) := by
    rw [CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 K g, ← map_mul]
    congr 1
    refine Units.ext ?_
    change (A : Matrix (Fin 3) (Fin 3) K) = ((A * (dGL3 d)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * ((dGL3 d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← Units.val_mul, inv_mul_cancel_right]
  have hgU : (projUnitriangular 3 K).map (MulAut.conj (proj 3 K g)).toMonoidHom =
      projUnitriangular 3 K := by
    have : MulAut.conj (proj 3 K g) = lConj 3 K A * (lConj 3 K (dGL3 d))⁻¹ := by
      rw [hgA, mul_inv_cancel_right]
    rw [this]
    exact map_mul_eq hA (map_inv_eq (map_lConj_dGL3 d))
  rw [hgA]
  exact mul_inv_mem_of_mul (map_lConj_dGL3 d)
    (conj_mul_inv_mem psl3_comm_mem (mem_normalizer_of_map_conj_eq hgU)) (lConj_dGL3_cent d)

theorem det_scalar3 (x : Kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) x) = x ^ 3 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Units.val_pow_eq_pow_val]
  simp

theorem mem_range_conj_of_lConj [Finite K] (A : GL (Fin 3) K)
    (h : ∃ k : ℕ, lConj 3 K A ^ 2 ^ k = 1) :
    lConj 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨k, hk⟩ := h
  rw [← map_pow] at hk
  have h1 : lConj 3 K (A ^ 2 ^ k) * lField 3 K 1 = 1 := by rw [map_one, mul_one, hk]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
  set d := Matrix.GeneralLinearGroup.det A
  have hdet : d ^ 2 ^ k = c ^ 3 := by
    have h2 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [map_pow, det_scalar3] at h2
    exact h2.symm
  have hb := Nat.gcd_eq_gcd_ab (2 ^ k) 3
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)),
    Nat.cast_one] at hb
  set u := Nat.gcdA (2 ^ k) 3
  set v := Nat.gcdB (2 ^ k) 3
  set μ : Kˣ := c ^ u * d ^ v
  have hμ : μ ^ 3 = d := by
    have e1 : μ ^ 3 = (c ^ 3) ^ u * d ^ (3 * v) := by
      rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul,
        ← zpow_natCast c 3, ← _root_.zpow_mul, mul_comm u, mul_comm v]
      rfl
    rw [e1, ← hdet, ← zpow_natCast d (2 ^ k), ← _root_.zpow_mul, ← _root_.zpow_add]
    conv_rhs => rw [← zpow_one d]
    congr 1
    push_cast at hb ⊢
    linarith
  have hdet1 : ((Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, det_scalar3, inv_pow, hμ,
      inv_mul_cancel, Units.val_one]
  let g : SL₃ := ⟨_, hdet1⟩
  refine ⟨proj 3 K g, ?_⟩
  rw [CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 K g]
  have : SpecialLinearGroup.toGL g = Matrix.GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A :=
    Units.ext rfl
  rw [this, map_mul, conjAut_scalar, one_mul]

end Linear

section Std

variable [CharP K 2]

theorem eq_one_of_sq_eq_one {x : Kˣ} (h : x ^ 2 = 1) : x = 1 := by
  have ht2 : (x : K) ^ 2 = 1 := by
    have := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have h3 : ((x : K) + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, ht2, one_pow, CharTwo.add_self_eq_zero]
  have h4 : (x : K) + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h3
  have h5 : (x : K) = -1 := eq_neg_of_add_eq_zero_left h4
  rw [CharTwo.neg_eq] at h5
  exact Units.ext h5

theorem stdL3_l3T (σ : K ≃+* K) (ε : ℕ) (a : Kˣ) :
    (lField 3 K σ * gammaL3 K ^ ε) (l3T K a) = l3T K (Units.map σ.toRingHom.toMonoidHom a) := by
  have hγ : (gammaL3 K ^ ε) (l3T K a) = l3T K a := by
    induction ε with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, gammaL3_l3T, ih]
  rw [MulAut.mul_apply, hγ, fieldAut_l3T]

theorem map_stdL3 [Finite K] (σ : K ≃+* K) (ε : ℕ) :
    (projUnitriangular 3 K).map (lField 3 K σ * gammaL3 K ^ ε).toMonoidHom =
      projUnitriangular 3 K :=
  map_mul_eq (map_fieldAut_projUnitriangular σ) (map_pow_eq map_gammaL3_projUnitriangular ε)

theorem comap_centMod_l3T [Finite K] (σ : K ≃+* K) (ε : ℕ) :
    (centMod (projUnitriangular 3 K) (lField 3 K σ * gammaL3 K ^ ε)).comap (l3T K) =
      unitsFix σ := by
  ext a
  rw [Subgroup.mem_comap, mem_centMod, stdL3_l3T, ← map_inv, ← map_mul, mem_unitsFix]
  constructor
  · intro h
    exact congrArg Units.val (mul_inv_eq_one.mp (l3T_mem_iff _ h.2))
  · intro h
    refine ⟨l3T_range_le ⟨a, rfl⟩, ?_⟩
    rw [mul_inv_eq_one.mpr (Units.ext h), map_one]
    exact one_mem _

theorem comap_centMod_l3T' [Finite K] :
    (centMod (projUnitriangular 3 K) (gammaL3 K)).comap (l3T' K) = rootsOfUnity 3 K := by
  ext b
  rw [Subgroup.mem_comap, mem_centMod, gammaL3_l3T', ← map_inv, ← map_mul, l3T'_mem_iff,
    mem_rootsOfUnity]
  have key : (b⁻¹ * b⁻¹) ^ 3 = 1 ↔ b ^ 3 = 1 := by
    constructor
    · intro h
      have h1 : ((b ^ 3)⁻¹) ^ 2 = 1 := by rw [← h]; group
      have h2 := eq_one_of_sq_eq_one h1
      rwa [inv_eq_one] at h2
    · intro h
      calc (b⁻¹ * b⁻¹) ^ 3 = ((b ^ 3)⁻¹) ^ 2 := by group
        _ = 1 := by rw [h, inv_one, one_pow]
  rw [key]
  exact ⟨fun h => h.2, fun h => ⟨l3T'_range_le ⟨b, rfl⟩, h⟩⟩

end Std

section Main

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem isPSL34_of_card (h4 : Nat.card K = 4) : IsPSL 3 2 2 (projectiveSL 3 K) :=
  ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, by rw [h4]; norm_num, ⟨(K1.statedProjEquivProjectiveSL 3 K).symm⟩⟩

theorem centMod_psl3 (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ)
    (h : (projUnitriangular 3 K).map (lConj 3 K A * (lField 3 K σ * gammaL3 K ^ ε)).toMonoidHom =
      projUnitriangular 3 K) :
    centMod (projUnitriangular 3 K) (lConj 3 K A * (lField 3 K σ * gammaL3 K ^ ε)) =
      centMod (projUnitriangular 3 K) (lField 3 K σ * gammaL3 K ^ ε) := by
  have hφ := map_stdL3 σ ε
  have hA : (projUnitriangular 3 K).map (lConj 3 K A).toMonoidHom = projUnitriangular 3 K := by
    have : lConj 3 K A = lConj 3 K A * (lField 3 K σ * gammaL3 K ^ ε) *
        (lField 3 K σ * gammaL3 K ^ ε)⁻¹ := by group
    rw [this]
    exact map_mul_eq h (map_inv_eq hφ)
  exact centMod_mul_eq hφ (lConj_cent A hA)

omit [CharP K 2] in
theorem card_le_four_of_forall_cube {hK4 : 4 ≤ Nat.card K}
    (h : ∀ b : Kˣ, b ^ 3 = 1) : Nat.card K = 4 := by
  have h1 : rootsOfUnity 3 K = ⊤ := eq_top_iff.mpr fun b _ => (mem_rootsOfUnity 3 b).mpr (h b)
  have h2 : Nat.card Kˣ ≤ 3 := by
    rw [← Subgroup.card_top (G := Kˣ), ← h1]
    exact card_rootsOfUnity K 3
  have h3 := Nat.card_eq_card_units_add_one K
  omega

theorem n4At_psl3 (hK4 : 4 ≤ Nat.card K) : N4At (projectiveSL 3 K) (projUnitriangular 3 K) := by
  intro α hα hαU hcent
  obtain ⟨A, σ, ε, hε, rfl⟩ := exists_conjAut_mul_std α
  rw [centMod_psl3 A σ ε hαU] at hcent
  have hσ : σ = 1 := by
    rw [← unitsFix_eq_top_iff, ← comap_centMod_l3T σ ε, eq_top_iff]
    intro a _
    exact hcent (l3T_range_le ⟨a, rfl⟩)
  subst hσ
  interval_cases ε
  · left
    rw [pow_zero, map_one, mul_one, mul_one] at hα ⊢
    exact mem_range_conj_of_lConj A hα
  · right
    rw [pow_one, map_one, one_mul] at hcent
    refine isPSL34_of_card (card_le_four_of_forall_cube (hK4 := hK4) fun b => ?_)
    have h1 : b ∈ (centMod (projUnitriangular 3 K) (gammaL3 K)).comap (l3T' K) :=
      hcent (l3T'_range_le ⟨b, rfl⟩)
    rw [comap_centMod_l3T'] at h1
    exact (mem_rootsOfUnity 3 b).mp h1

theorem n2At_psl3 (hK4 : 4 ≤ Nat.card K) : N2At (projectiveSL 3 K) (projUnitriangular 3 K) := by
  intro α hα hαU hidx
  obtain ⟨A, σ, ε, hε, rfl⟩ := exists_conjAut_mul_std α
  rw [centMod_psl3 A σ ε hαU] at hidx
  have h1 := index_comap_le (projUnitriangular 3 K) (lField 3 K σ * gammaL3 K ^ ε) (l3T K)
    l3T_range_le
  rw [comap_centMod_l3T, hidx] at h1
  refine Or.inr (Or.inr (isPSL34_of_card ?_))
  rcases eq_one_or_card_eq_four_of_index_unitsFix_le_three h1 with hσ | h4
  · subst hσ
    interval_cases ε
    · exfalso
      rw [pow_zero, map_one, mul_one, centMod_one, Subgroup.relIndex_self] at hidx
      omega
    · rw [pow_one, map_one, one_mul] at hidx
      have h2 := index_comap_le (projUnitriangular 3 K) (gammaL3 K) (l3T' K) l3T'_range_le
      rw [comap_centMod_l3T', hidx] at h2
      have h3 := (rootsOfUnity 3 K).card_mul_index
      have h4 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
      have h5 := Nat.card_eq_card_units_add_one K
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨m, -, hm⟩ := FiniteField.card K 2
      rw [Nat.card_eq_fintype_card] at h5 hK4 ⊢
      rw [hm] at h5 hK4 ⊢
      have hm3 : (m : ℕ) ≤ 3 := by
        by_contra hm3
        have : 2 ^ 4 ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
      have hm2 : 2 ≤ (m : ℕ) := by
        by_contra hm2
        have : 2 ^ (m : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases (m : ℕ)
      · rfl
      · exfalso
        have h7 : Nat.card Kˣ = 7 := by omega
        have h8 : Nat.card (rootsOfUnity 3 K) ∣ 7 := h7 ▸ Subgroup.card_subgroup_dvd_card _
        rcases (Nat.dvd_prime (by norm_num)).mp h8 with h9 | h9 <;> nlinarith
  · exact h4

theorem isSylowTwoOf_projUnitriangular_three : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  rw [← hP]
  exact isSylowTwoOf_sylow P

end Main

end L3

theorem n2Model_n4Model_of_isPSL3 {M : Type} [Group M] {n : ℕ} (hn : 1 < n)
    (h : IsPSL 3 2 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let e' : M ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  exact ⟨(N2Model.of_at isSylowTwoOf_projUnitriangular_three (n2At_psl3 hK4)).of_mulEquiv e'.symm,
    (N4Model.of_at isSylowTwoOf_projUnitriangular_three (n4At_psl3 hK4)).of_mulEquiv e'.symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
