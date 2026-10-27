module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.DegreeFiveSection

open CFSG CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def pauliGen : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | 1 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
  | 2 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 3 => !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

@[expose] def pauliInt (v : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) ℤ :=
  (if v 0 = 1 then pauliGen 0 else 1) * (if v 1 = 1 then pauliGen 1 else 1) *
    (if v 2 = 1 then pauliGen 2 else 1) * (if v 3 = 1 then pauliGen 3 else 1)

theorem pauliInt_zero : pauliInt 0 = 1 := by decide

theorem pauliInt_mul : ∀ v w : Fin 4 → ZMod 2,
    pauliInt v * pauliInt w = pauliInt (v + w) ∨ pauliInt v * pauliInt w = -pauliInt (v + w) := by
  decide

theorem pauliInt_det : ∀ v : Fin 4 → ZMod 2, (pauliInt v).det = 1 := by decide

theorem pauliInt_transpose_mul : ∀ v : Fin 4 → ZMod 2, (pauliInt v)ᵀ * pauliInt v = 1 := by
  decide

theorem pauliInt_mul_transpose : ∀ v : Fin 4 → ZMod 2, pauliInt v * (pauliInt v)ᵀ = 1 := by
  decide

theorem pauliInt_nonscalar : ∀ v : Fin 4 → ZMod 2, v = 0 ∨ ∃ ij : Fin 4 × Fin 4,
    pauliInt v ij.1 ij.2 ≠ 0 ∧ (ij.1 ≠ ij.2 ∨ pauliInt v ij.1 ij.2 ≠ pauliInt v 0 0) := by
  decide

theorem pauliInt_entries : ∀ (v : Fin 4 → ZMod 2) (ij : Fin 4 × Fin 4),
    pauliInt v ij.1 ij.2 = 0 ∨ pauliInt v ij.1 ij.2 = 1 ∨ pauliInt v ij.1 ij.2 = -1 := by
  decide

section Field

variable {K : Type} [Field K]

abbrev pauliMat (v : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) K :=
  (pauliInt v).map (Int.castRingHom K)

@[expose] def pauliGL (v : Fin 4 → ZMod 2) : GL (Fin 4) K :=
  ⟨pauliMat v, (pauliMat v)ᵀ, by
    rw [pauliMat, ← Matrix.transpose_map, ← Matrix.map_mul, pauliInt_mul_transpose,
      Matrix.map_one _ (map_zero _) (map_one _)], by
    rw [pauliMat, ← Matrix.transpose_map, ← Matrix.map_mul, pauliInt_transpose_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem coe_pauliGL (v : Fin 4 → ZMod 2) :
    ((pauliGL v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = pauliMat v := rfl

theorem det_pauliMat (v : Fin 4 → ZMod 2) : (pauliMat (K := K) v).det = 1 := by
  rw [pauliMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, pauliInt_det, map_one]

theorem pauliMat_transpose_mul (v : Fin 4 → ZMod 2) :
    (pauliMat (K := K) v)ᵀ * pauliMat v = 1 := by
  rw [pauliMat, ← Matrix.transpose_map, ← Matrix.map_mul, pauliInt_transpose_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem pauliMat_map (σ : K ≃+* K) (v : Fin 4 → ZMod 2) :
    (pauliMat (K := K) v).map σ = pauliMat v :=
  Matrix.ext fun i j => by simp only [pauliMat, Matrix.map_apply, eq_intCast, map_intCast]

theorem int_eq_of_cast_eq (h2 : (2 : K) ≠ 0) {a b : ℤ} (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) (h : (a : K) = b) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> push_cast at h
  all_goals first
    | rfl
    | exact absurd (show (1 : K) = 0 by linear_combination h) one_ne_zero
    | exact absurd (show (1 : K) = 0 by linear_combination -h) one_ne_zero
    | exact absurd (show (2 : K) = 0 by linear_combination h) h2
    | exact absurd (show (2 : K) = 0 by linear_combination -h) h2

theorem eq_zero_of_pauliMat_eq_scalar (h2 : (2 : K) ≠ 0) {v : Fin 4 → ZMod 2} {c : K}
    (hc : pauliMat (K := K) v = Matrix.scalar (Fin 4) c) : v = 0 := by
  rcases pauliInt_nonscalar v with h | ⟨⟨i, j⟩, hij0, hij⟩
  · exact h
  have hentry : ∀ a b : Fin 4, ((pauliInt v a b : ℤ) : K) = if a = b then c else 0 := by
    intro a b
    have := congrFun (congrFun hc a) b
    rw [Matrix.scalar_apply, Matrix.diagonal_apply] at this
    exact this
  exfalso
  rcases hij with hne | hne
  · have h1 := hentry i j
    rw [ite_eq_right hne] at h1
    exact hij0 (int_eq_of_cast_eq h2 (pauliInt_entries v (i, j)) (Or.inl rfl) (by
      rw [h1, Int.cast_zero]))
  · have h1 := hentry i j
    have h0 := hentry 0 0
    by_cases hij' : i = j
    · rw [ite_eq_left hij'] at h1
      rw [ite_eq_left rfl] at h0
      exact hne (int_eq_of_cast_eq h2 (pauliInt_entries v (i, j)) (pauliInt_entries v (0, 0))
        (by rw [h1, h0]))
    · rw [ite_eq_right hij'] at h1
      exact hij0 (int_eq_of_cast_eq h2 (pauliInt_entries v (i, j)) (Or.inl rfl) (by
        rw [h1, Int.cast_zero]))

theorem exists_pauli_hom (h2 : (2 : K) ≠ 0) (G4 : Subgroup (GL (Fin 4) K))
    (hP : ∀ v, pauliGL (K := K) v ∈ G4) :
    ∃ Ψ : Multiplicative (Fin 4 → ZMod 2) →* StatedProj G4, Function.Injective Ψ := by
  set N := (StatedScalars (Fin 4) K).subgroupOf G4
  let F : (Fin 4 → ZMod 2) → StatedProj G4 := fun v => QuotientGroup.mk' N ⟨pauliGL v, hP v⟩
  have hF0 : F 0 = 1 := by
    have h1 : (⟨pauliGL 0, hP 0⟩ : G4) = 1 := Subtype.ext (Units.ext (by
      rw [coe_pauliGL, pauliMat, pauliInt_zero, Matrix.map_one _ (map_zero _) (map_one _)]
      rfl))
    change QuotientGroup.mk' N _ = 1
    rw [h1, map_one]
  have hFmul : ∀ v w, F (v + w) = F v * F w := by
    intro v w
    change QuotientGroup.mk' N _ = QuotientGroup.mk' N _ * QuotientGroup.mk' N _
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases pauliInt_mul v w with h | h
    · have hgl : pauliGL (K := K) v * pauliGL (K := K) w = pauliGL (K := K) (v + w) :=
        Units.ext (by
        rw [Units.val_mul, coe_pauliGL, coe_pauliGL, coe_pauliGL, pauliMat, pauliMat, pauliMat,
          ← Matrix.map_mul, h])
      rw [hgl, inv_mul_cancel]
      exact one_mem _
    · have hgl : pauliGL (K := K) v * pauliGL (K := K) w = -pauliGL (K := K) (v + w) :=
        Units.ext (by
        rw [Units.val_mul, Units.val_neg, coe_pauliGL, coe_pauliGL, coe_pauliGL, pauliMat,
          pauliMat, pauliMat, ← Matrix.map_mul, h, Matrix.map_neg _ fun a => map_neg _ a])
      rw [hgl, inv_neg, neg_mul, inv_mul_cancel]
      refine ⟨-1, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_neg, Units.val_one,
        Units.val_one, map_neg, map_one]
  let Ψ : Multiplicative (Fin 4 → ZMod 2) →* StatedProj G4 :=
    { toFun := fun v => F (Multiplicative.toAdd v)
      map_one' := hF0
      map_mul' := fun v w => hFmul _ _ }
  refine ⟨Ψ, (injective_iff_map_eq_one Ψ).mpr fun v hv => ?_⟩
  change QuotientGroup.mk' N _ = 1 at hv
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv
  obtain ⟨c, hc⟩ := hv
  have hc' : (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) =
      pauliGL (K := K) (Multiplicative.toAdd v) := hc
  have hmat : pauliMat (K := K) (Multiplicative.toAdd v) = Matrix.scalar (Fin 4) (c : K) := by
    rw [← coe_pauliGL, ← hc', Matrix.GeneralLinearGroup.coe_scalar]
  exact Multiplicative.toAdd.injective (eq_zero_of_pauliMat_eq_scalar h2 hmat)

end Field

theorem range_isElementaryAbelian_of_injective {S : Type*} [Group S]
    (Ψ : Multiplicative (Fin 4 → ZMod 2) →* S) (hΨ : Function.Injective Ψ) :
    IsElementaryAbelian 2 Ψ.range ∧ Nat.card Ψ.range = 16 := by
  have hcomm : ∀ x y : Ψ.range, x * y = y * x := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    change Ψ a * Ψ b = Ψ b * Ψ a
    rw [← map_mul, ← map_mul, mul_comm]
  have hsq : ∀ x : Ψ.range, x ^ 2 = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    change Ψ a ^ 2 = 1
    have ha : a ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      have h : ∀ x : ZMod 2, 2 • x = 0 := by decide
      exact h _
    rw [← map_pow, ha, map_one]
  refine ⟨{ toIsMulCommutative := ⟨⟨hcomm⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ _), Nat.card_fun,
    Nat.card_zmod, Nat.card_fin]
  norm_num

section Block

variable (K : Type) [Field K]

@[expose] noncomputable def blockFive : Matrix (Fin 4) (Fin 4) K →* Matrix (Fin 5) (Fin 5) K where
  toFun A := Matrix.reindexAlgEquiv K K finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) K))
  map_one' := by rw [Matrix.fromBlocks_one, map_one]
  map_mul' A B := by
    change Matrix.reindexAlgEquiv K K finSumFinEquiv (Matrix.fromBlocks (A * B) 0 0 1) =
      Matrix.reindexAlgEquiv K K finSumFinEquiv (Matrix.fromBlocks A 0 0 1) *
        Matrix.reindexAlgEquiv K K finSumFinEquiv (Matrix.fromBlocks B 0 0 1)
    rw [← map_mul, Matrix.fromBlocks_multiply]
    simp

@[expose] noncomputable def blockFiveGL : GL (Fin 4) K →* GL (Fin 5) K :=
  Units.map (blockFive K)

variable {K}

theorem blockFive_apply (A : Matrix (Fin 4) (Fin 4) K) :
    blockFive K A = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) K)) := by
  rw [← Matrix.coe_reindexAlgEquiv K K]
  rfl

theorem blockFive_castAdd (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    blockFive K A (Fin.castAdd 1 i) (Fin.castAdd 1 j) = A i j := by
  rw [blockFive_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]

theorem blockFive_last (A : Matrix (Fin 4) (Fin 4) K) :
    blockFive K A (Fin.last 4) (Fin.last 4) = 1 := by
  rw [blockFive_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last,
    Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]

theorem det_blockFive (A : Matrix (Fin 4) (Fin 4) K) : (blockFive K A).det = A.det := by
  rw [blockFive_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]

theorem blockFive_map (σ : K → K) (h0 : σ 0 = 0) (h1 : σ 1 = 1) (A : Matrix (Fin 4) (Fin 4) K) :
    (blockFive K A).map σ = blockFive K (A.map σ) := by
  rw [blockFive_apply, blockFive_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero _ h0,
    Matrix.map_zero _ h0, Matrix.map_one _ h0 h1]

theorem blockFive_transpose (A : Matrix (Fin 4) (Fin 4) K) :
    (blockFive K A)ᵀ = blockFive K Aᵀ := by
  rw [blockFive_apply, blockFive_apply, Matrix.transpose_reindex, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]

theorem eq_one_of_blockFive_eq_scalar {g : Matrix (Fin 4) (Fin 4) K} {c : K}
    (hc : blockFive K g = Matrix.scalar (Fin 5) c) : g = 1 := by
  have hlast := congrFun (congrFun hc (Fin.last 4)) (Fin.last 4)
  rw [blockFive_last, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hlast
  ext i j
  have h := congrFun (congrFun hc (Fin.castAdd 1 i)) (Fin.castAdd 1 j)
  rw [blockFive_castAdd, Matrix.scalar_apply, Matrix.diagonal_apply, ← hlast] at h
  rw [h, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [ite_eq_right hij, ite_eq_right fun h' => hij (Fin.castAdd_injective 4 1 h')]

end Block

section Section

variable {K : Type} [Field K]

theorem exists_quasisimple_section (h2 : (2 : K) ≠ 0) (G4 : Subgroup (GL (Fin 4) K))
    (G5 : Subgroup (GL (Fin 5) K)) (hblk : ∀ g ∈ G4, blockFiveGL K g ∈ G5)
    (hneg : (-1 : GL (Fin 4) K) ∈ G4) (hq : CFSG.IsQuasisimple G4)
    (hZ : Subgroup.center G4 = (StatedScalars (Fin 4) K).subgroupOf G4)
    {T : Type} [Group T] (e : T ≃* StatedProj G5) :
    ∃ M : Subgroup T, CFSG.IsQuasisimple M ∧ Even (Nat.card (Subgroup.center M)) ∧
      Nonempty (M ⧸ Subgroup.center M ≃* StatedProj G4) := by
  let θ₀ : G4 →* G5 := ((blockFiveGL K).comp G4.subtype).codRestrict G5 fun g => hblk g g.2
  let θ : G4 →* T := e.symm.toMonoidHom.comp
    ((QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf G5)).comp θ₀)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf G5) (θ₀ g) = 1 :=
      e.symm.injective (by rw [map_one]; exact hg)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    obtain ⟨c, hc⟩ := h1
    have hmat : blockFive K ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.scalar (Fin 5) (c : K) := by
      have h3 := congrArg (fun x : GL (Fin 5) K => (x : Matrix (Fin 5) (Fin 5) K)) hc
      rw [Matrix.GeneralLinearGroup.coe_scalar] at h3
      exact h3.symm
    exact Subtype.ext (Units.ext (eq_one_of_blockFive_eq_scalar hmat))
  let eM : G4 ≃* θ.range := MonoidHom.ofInjective hθ
  refine ⟨θ.range, LocalCores.isQuasisimple_of_mulEquiv eM hq, ?_, ?_⟩
  ·
    rw [← Nat.card_congr (Subgroup.centerCongr eM).toEquiv]
    have hmem : (⟨-1, hneg⟩ : G4) ∈ Subgroup.center G4 := by
      rw [hZ, Subgroup.mem_subgroupOf]
      refine ⟨-1, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_neg, Units.val_one,
        Units.val_one, map_neg, map_one]
    have hne : (⟨⟨-1, hneg⟩, hmem⟩ : Subgroup.center G4) ≠ 1 := by
      intro h1
      have h3 := congrArg (fun x : Subgroup.center G4 =>
        (((x : G4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h1
      simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq,
        OneMemClass.coe_one] at h3
      exact h2 (by linear_combination -h3)
    have hsq : (⟨⟨-1, hneg⟩, hmem⟩ : Subgroup.center G4) ^ 2 = 1 :=
      Subtype.ext (Subtype.ext (by
        change ((-1 : GL (Fin 4) K)) ^ 2 = 1
        rw [neg_one_sq]))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord := orderOf_eq_prime hsq hne
    exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)
  · exact ⟨(QuotientGroup.congr (Subgroup.center θ.range) (Subgroup.center G4) eM.symm
      (Subgroup.map_center_eq eM.symm)).trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩

end Section

section Cases

variable {K : Type} [Field K]

omit [Field K] in
theorem two_ne_zero_of_charP [Field K] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) [CharP K ℓ] :
    (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K ℓ] at h'
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')

theorem mem_statedSL_iff' {n : ℕ} (g : GL (Fin n) K) :
    g ∈ StatedSL n K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem center_statedSL_eq_scalars (n : ℕ) :
    Subgroup.center (StatedSL n K) = (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
  rw [← map_center_eq_statedScalars, Subgroup.map_center_eq]

theorem linear_case (h2 : (2 : K) ≠ 0) {T : Type} [Group T] (e : T ≃* StatedProj (StatedSL 5 K)) :
    ∃ M : Subgroup T, CFSG.IsQuasisimple M ∧ Even (Nat.card (Subgroup.center M)) ∧
      Nonempty (M ⧸ Subgroup.center M ≃* StatedProj (StatedSL 4 K)) ∧
      ∃ E : Subgroup (M ⧸ Subgroup.center M), IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  have hblk : ∀ g ∈ StatedSL 4 K, blockFiveGL K g ∈ StatedSL 5 K := by
    intro g hg
    rw [mem_statedSL_iff'] at hg ⊢
    change (blockFive K (g : Matrix (Fin 4) (Fin 4) K)).det = 1
    rw [det_blockFive, hg]
  have hneg : (-1 : GL (Fin 4) K) ∈ StatedSL 4 K := by
    rw [mem_statedSL_iff', Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one,
      Fintype.card_fin]
    norm_num
  have hq : CFSG.IsQuasisimple (StatedSL 4 K) := LocalCores.isQuasisimple_of_mulEquiv
    (specialLinearGroupEquivStatedSL 4 K)
    (Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  obtain ⟨M, hMq, hMeven, ⟨eS⟩⟩ := exists_quasisimple_section h2 (StatedSL 4 K) (StatedSL 5 K)
    hblk hneg hq (center_statedSL_eq_scalars 4) e
  obtain ⟨Ψ, hΨ⟩ := exists_pauli_hom h2 (StatedSL 4 K) fun v => by
    rw [mem_statedSL_iff', coe_pauliGL, det_pauliMat]
  obtain ⟨hab, hcard⟩ := range_isElementaryAbelian_of_injective (eS.symm.toMonoidHom.comp Ψ)
    (eS.symm.injective.comp hΨ)
  exact ⟨M, hMq, hMeven, ⟨eS⟩, _, hab, hcard⟩

variable [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem mem_statedSU_iff' (hK : Nat.card K = (ℓ ^ f) ^ 2) {n : ℕ} (g : GL (Fin n) K) :
    g ∈ StatedSU n (ℓ ^ f) K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 ∧
      CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f)
        (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n]
  exact CFSG.LieType.Universal.Unitary.mem_SUid

theorem unitary_case (h2 : (2 : K) ≠ 0) (hK : Nat.card K = (ℓ ^ f) ^ 2) {T : Type} [Group T]
    (e : T ≃* StatedProj (StatedSU 5 (ℓ ^ f) K)) :
    ∃ M : Subgroup T, CFSG.IsQuasisimple M ∧ Even (Nat.card (Subgroup.center M)) ∧
      Nonempty (M ⧸ Subgroup.center M ≃* StatedProj (StatedSU 4 (ℓ ^ f) K)) ∧
      ∃ E : Subgroup (M ⧸ Subgroup.center M), IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K ℓ f
  have hblk : ∀ g ∈ StatedSU 4 (ℓ ^ f) K, blockFiveGL K g ∈ StatedSU 5 (ℓ ^ f) K := by
    intro g hg
    rw [mem_statedSU_iff' hK] at hg ⊢
    change (blockFive K (g : Matrix (Fin 4) (Fin 4) K)).det = 1 ∧
      CFSG.LieType.Universal.Unitary.conjTr σ (blockFive K (g : Matrix (Fin 4) (Fin 4) K)) *
        blockFive K (g : Matrix (Fin 4) (Fin 4) K) = 1
    refine ⟨by rw [det_blockFive, hg.1], ?_⟩
    rw [CFSG.LieType.Universal.Unitary.conjTr, blockFive_map σ (map_zero σ) (map_one σ),
      blockFive_transpose, ← map_mul]
    change blockFive K (CFSG.LieType.Universal.Unitary.conjTr σ (g : Matrix (Fin 4) (Fin 4) K) *
      (g : Matrix (Fin 4) (Fin 4) K)) = 1
    rw [hg.2, map_one]
  have hneg : (-1 : GL (Fin 4) K) ∈ StatedSU 4 (ℓ ^ f) K := by
    rw [mem_statedSU_iff' hK, Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one,
      Fintype.card_fin, CFSG.LieType.Universal.Unitary.conjTr]
    refine ⟨by norm_num, ?_⟩
    rw [Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_neg, Matrix.transpose_one, neg_mul_neg, Matrix.one_mul]
  have hqZ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 4) hK
    (by norm_num) (by simp)
  obtain ⟨M, hMq, hMeven, ⟨eS⟩⟩ := exists_quasisimple_section h2 (StatedSU 4 (ℓ ^ f) K)
    (StatedSU 5 (ℓ ^ f) K) hblk hneg hqZ.1 hqZ.2 e
  obtain ⟨Ψ, hΨ⟩ := exists_pauli_hom h2 (StatedSU 4 (ℓ ^ f) K) fun v => by
    rw [mem_statedSU_iff' hK, coe_pauliGL, det_pauliMat, CFSG.LieType.Universal.Unitary.conjTr,
      pauliMat_map σ]
    exact ⟨rfl, pauliMat_transpose_mul v⟩
  obtain ⟨hab, hcard⟩ := range_isElementaryAbelian_of_injective (eS.symm.toMonoidHom.comp Ψ)
    (eS.symm.injective.comp hΨ)
  exact ⟨M, hMq, hMeven, ⟨eS⟩, _, hab, hcard⟩

end Cases

theorem degree_five_classical_even_center_four_dimensional_section {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2)
    {c : StatedLieTag} (hc : c = .PSL ∨ c = .PSU) (T : Type) [Group T]
    (hT : StatedClassicalModel T c 5 ℓ f) :
    ∃ M : Subgroup T, CFSG.IsQuasisimple M ∧ Even (Nat.card (Subgroup.center M)) ∧
      StatedClassicalModel (M ⧸ Subgroup.center M) c 4 ℓ f ∧
      ∃ E : Subgroup (M ⧸ Subgroup.center M), IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  rcases hc with rfl | rfl
  · obtain ⟨⟨hℓ, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hT
    have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      hf hK
    obtain ⟨M, hMq, hMeven, ⟨eS⟩, E, hE⟩ := linear_case (two_ne_zero_of_charP hℓ hℓ2) e
    exact ⟨M, hMq, hMeven, ⟨⟨hℓ, hf, by norm_num, by simp, by simp⟩, K, inferInstance,
      inferInstance, hK, ⟨eS⟩⟩, E, hE⟩
  · obtain ⟨⟨hℓ, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hT
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
    obtain ⟨M, hMq, hMeven, ⟨eS⟩, E, hE⟩ := unitary_case (two_ne_zero_of_charP hℓ hℓ2) hK e
    exact ⟨M, hMq, hMeven, ⟨⟨hℓ, hf, by norm_num, by simp⟩, K, inferInstance, inferInstance,
      hK, ⟨eS⟩⟩, E, hE⟩

end CFSG.RankThree.DegreeFiveSection
