module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitaryDiag
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestAssembly

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank InnerDiagSU

namespace MpStdSU

section Transport

variable {F K : Type*} [Field F] [Field K] (τ : F ≃+* K) {n : ℕ}

@[expose] noncomputable def glMap : GL (Fin n) F ≃* GL (Fin n) K :=
  Units.mapEquiv τ.mapMatrix.toMulEquiv

theorem coe_glMap (B : GL (Fin n) F) :
    ((glMap τ B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) F).map τ :=
  rfl

theorem coe_glMap_symm (B : GL (Fin n) K) :
    (((glMap τ).symm B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (B : Matrix (Fin n) (Fin n) K).map τ.symm :=
  rfl

variable {σF : F ≃+* F} {σK : K ≃+* K}

theorem conjTr_map (hτ : ∀ x, τ (σF x) = σK (τ x)) (M : Matrix (Fin n) (Fin n) F) :
    conjTr σK (M.map τ) = (conjTr σF M).map τ := by
  ext a b
  simp [conjTr, hτ]

theorem glMap_mem_SUid (hτ : ∀ x, τ (σF x) = σK (τ x)) {B : GL (Fin n) F}
    (hB : B ∈ SUid σF n) : glMap τ B ∈ SUid σK n := by
  obtain ⟨hdet, hiso⟩ := hB
  refine ⟨?_, ?_⟩
  · have h := RingHom.map_det τ.toRingHom (B : Matrix (Fin n) (Fin n) F)
    rw [hdet, map_one] at h
    exact h.symm
  · rw [coe_glMap, conjTr_map τ hτ, ← Matrix.map_mul, hiso]
    exact Matrix.map_one _ (map_zero τ) (map_one τ)

@[expose] noncomputable def suidEquiv (hτ : ∀ x, τ (σF x) = σK (τ x))
    (hτ' : ∀ y, τ.symm (σK y) = σF (τ.symm y)) : SUid σF n ≃* SUid σK n where
  toFun B := ⟨glMap τ B, glMap_mem_SUid τ hτ B.2⟩
  invFun B := ⟨(glMap τ).symm B, glMap_mem_SUid τ.symm hτ' B.2⟩
  left_inv B := Subtype.ext ((glMap τ).symm_apply_apply (B : GL (Fin n) F))
  right_inv B := Subtype.ext ((glMap τ).apply_symm_apply (B : GL (Fin n) K))
  map_mul' B C := Subtype.ext (map_mul (glMap τ) (B : GL (Fin n) F) (C : GL (Fin n) F))

theorem coe_suidEquiv (hτ : ∀ x, τ (σF x) = σK (τ x))
    (hτ' : ∀ y, τ.symm (σK y) = σF (τ.symm y)) (B : SUid σF n) :
    ((suidEquiv τ hτ hτ' B : SUid σK n) : GL (Fin n) K) = glMap τ B :=
  rfl

end Transport

theorem unitaryInvolution_map {F K : Type} [Field F] [Field K] [Finite F] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP F p] [CharP K p] (τ : F ≃+* K) (x : F) :
    τ (unitaryInvolution F p f x) = unitaryInvolution K p f (τ x) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]

section Std

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (τ : F ≃+* K)
  {n : ℕ} (P : GL (Fin n) F)
  (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
    (P : Matrix (Fin n) (Fin n) F) = antidiag n)

@[expose] noncomputable def suEquiv :
    SU (unitaryInvolution F 2 f) n ≃* LargeEvenSUGroup (Fin n) K (2 ^ f) :=
  (conjEquiv P hP).trans ((suidEquiv τ (unitaryInvolution_map τ)
    (unitaryInvolution_map τ.symm)).trans (MulEquiv.subgroupCongr
      (SUid_eq_statedSU hK n : SUid (unitaryInvolution K 2 f) n =
        LargeEvenSUGroup (Fin n) K (2 ^ f))))

theorem coe_suEquiv (u : SU (unitaryInvolution F 2 f) n) :
    ((suEquiv hK τ P hP u : LargeEvenSUGroup (Fin n) K (2 ^ f)) : GL (Fin n) K) =
      glMap τ (P * (u : GL (Fin n) F) * P⁻¹) :=
  rfl

@[expose] noncomputable def stdProj :
    SU (unitaryInvolution F 2 f) n →* LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)) :=
  (LargeEvenProjMk _).comp (suEquiv hK τ P hP).toMonoidHom

theorem stdProj_surjective : Function.Surjective (stdProj hK τ P hP) :=
  (QuotientGroup.mk'_surjective _).comp (suEquiv hK τ P hP).surjective

theorem ker_stdProj (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    (stdProj hK τ P hP).ker = Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
  have hZ : Subgroup.center ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) =
      (LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K (2 ^ f)) :=
    (isQuasisimple_statedSU_of_card hK hn hnq).2
  ext u
  rw [MonoidHom.mem_ker]
  show (QuotientGroup.mk (s := (LargeEvenScalars (Fin n) K).subgroupOf _) (suEquiv hK τ P hP u) :
    LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f))) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, ← hZ]
  exact MpLinear.apply_mem_center_iff (suEquiv hK τ P hP)

variable {G : Type*} [Group G] (ψ : SU (unitaryInvolution F 2 f) n →* G)

@[expose] noncomputable def rangeProj :
    SU (unitaryInvolution F 2 f) n →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
  (QuotientGroup.mk' _).comp ψ.rangeRestrict

theorem rangeProj_surjective : Function.Surjective (rangeProj ψ) :=
  (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective

theorem ker_rangeProj (hperf : commutator (SU (unitaryInvolution F 2 f) n) = ⊤)
    (hker : ψ.ker ≤ Subgroup.center _) :
    (rangeProj ψ).ker = Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
  ext u
  rw [MonoidHom.mem_ker]
  show (QuotientGroup.mk (ψ.rangeRestrict u) : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hker, fun hu => ?_⟩
  rw [Subgroup.mem_center_iff]
  intro l
  obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]

@[expose] noncomputable def stdEquiv (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (hker : ψ.ker ≤ Subgroup.center _) :
    ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)) :=
  (QuotientGroup.quotientKerEquivOfSurjective (rangeProj ψ) (rangeProj_surjective ψ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      ((ker_rangeProj ψ (isQuasisimple_SU hF hn hnq).1.commutator_eq_top hker).trans
        (ker_stdProj hK τ P hP hn hnq).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (stdProj hK τ P hP) (stdProj_surjective hK τ P hP)))

theorem stdEquiv_rangeProj (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (hker : ψ.ker ≤ Subgroup.center _) (u : SU (unitaryInvolution F 2 f) n) :
    stdEquiv hF hK τ P hP ψ hn hnq hker (rangeProj ψ u) = stdProj hK τ P hP u := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (rangeProj ψ)
      (rangeProj_surjective ψ)).symm (rangeProj ψ u) =
      (u : SU (unitaryInvolution F 2 f) n ⧸ (rangeProj ψ).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [stdEquiv, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end Std

section UnitaryConj

theorem conjTr_smul {K : Type*} [Field K] (σ : K ≃+* K) {n : ℕ} (c : K)
    (M : Matrix (Fin n) (Fin n) K) : conjTr σ (c • M) = σ c • conjTr σ M := by
  ext a b
  simp [conjTr]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
  {n : ℕ}

include hK in
theorem mem_normalizer_of_isIdUnitary {B : GL (Fin n) K}
    (hB : IsIdUnitary (unitaryInvolution K 2 f) B) :
    B ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K (2 ^ f) : Set (GL (Fin n) K)) := by
  have e : SUid (unitaryInvolution K 2 f) n = LargeEvenSUGroup (Fin n) K (2 ^ f) :=
    SUid_eq_statedSU hK n
  rw [← e]
  exact mem_normalizer_SUid hB

include hK in
theorem exists_isIdUnitary_of_mem_GUSet {A : GL (Fin n) K}
    (hA : A ∈ LargeEvenGUSet (Fin n) K (2 ^ f)) : ∃ l : Kˣ,
      IsIdUnitary (unitaryInvolution K 2 f) (Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ * A) := by
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hq : 2 ≤ 2 ^ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨l, hl⟩ := TableB.exists_norm_eq hq hK hμ0 hμq
  refine ⟨l, ?_⟩
  have hmap : (A : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K 2 f) =
      (A : Matrix (Fin n) (Fin n) K).map (· ^ 2 ^ f) := by
    ext a b
    simp only [Matrix.map_apply, unitaryInvolution_apply]
  unfold IsIdUnitary
  rw [TableB.coe_scalar_mul, conjTr_smul, Matrix.smul_mul, Matrix.mul_smul, conjTr, hmap, hAμ,
    smul_smul, smul_smul, unitaryInvolution_apply, ← hl]
  have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
  have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ f * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ f + 1) = 1 := by
    calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ f * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ f + 1) =
          (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ f * (((l⁻¹ : Kˣ) : K) * l) := by ring
      _ = 1 := by rw [hinv, one_pow, one_mul]
  rw [h0, one_smul]

omit [Finite K] [CharP K 2] in
theorem IsIdUnitary.mul' {σ : K ≃+* K} {A B : GL (Fin n) K} (hA : IsIdUnitary σ A)
    (hB : IsIdUnitary σ B) : IsIdUnitary σ (A * B) := by
  unfold IsIdUnitary at hA hB ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr σ (B : Matrix (Fin n) (Fin n) K) * conjTr σ (A : Matrix (Fin n) (Fin n) K) *
        ((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K))
      = conjTr σ (B : Matrix (Fin n) (Fin n) K) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) *
            (B : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

@[expose] noncomputable def unitaryNorm (K : Type) [Field K] [Finite K] [CharP K 2] (f n : ℕ) :
    Subgroup (Subgroup.normalizer (LargeEvenSUGroup (Fin n) K (2 ^ f) : Set (GL (Fin n) K))) where
  carrier := {B | IsIdUnitary (unitaryInvolution K 2 f) (B : GL (Fin n) K)}
  mul_mem' hA hB := IsIdUnitary.mul' hA hB
  one_mem' := by
    show conjTr _ ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_one, conjTr_one, Matrix.one_mul]
  inv_mem' hA := IsIdUnitary.inv hA

include hK in
theorem ggInndiag_le_unitaryNorm :
    ggInndiag (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)))
          (LargeEvenGUSet (Fin n) K (2 ^ f))) ≤
      (unitaryNorm K f n).map (TableB.projConj (LargeEvenSUGroup (Fin n) K (2 ^ f))) := by
  have e : SUid (unitaryInvolution K 2 f) n = LargeEvenSUGroup (Fin n) K (2 ^ f) :=
    SUid_eq_statedSU hK n
  have hN : LargeEvenGUSet (Fin n) K (2 ^ f) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin n) K (2 ^ f) : Set (GL (Fin n) K)) := by
    intro A hA
    obtain ⟨l, hl⟩ := exists_isIdUnitary_of_mem_GUSet hK hA
    have e' : A = Matrix.GeneralLinearGroup.scalar (Fin n) l *
        (Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ * A) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [e']
    exact mul_mem (TableB.scalar_mem_normalizer _ ⟨l, rfl⟩) (mem_normalizer_of_isIdUnitary hK hl)
  refine sup_le ?_ ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨r, rfl⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
    have hh : (h : GL (Fin n) K) ∈ SUid (unitaryInvolution K 2 f) n := by
      rw [e]
      exact h.2
    refine ⟨⟨h, Subgroup.le_normalizer h.2⟩, hh.2, ?_⟩
    rw [TableB.projConj_of_mem _ (h : GL (Fin n) K) h.2]
  · intro φ hφ
    obtain ⟨A, hA, rfl⟩ := TableB.exists_eq_projConj hN hφ
    obtain ⟨l, hl⟩ := exists_isIdUnitary_of_mem_GUSet hK hA
    refine ⟨⟨_, mem_normalizer_of_isIdUnitary hK hl⟩, hl, ?_⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H h =>
      rw [TableB.projConj_mk, TableB.projConj_mk]
      congr 1
      apply Subtype.ext
      show Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ * A * h *
          (Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹ * A)⁻¹ = A * h * A⁻¹
      have hc := Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin n) l⁻¹)
      set z := Matrix.GeneralLinearGroup.scalar (Fin n) l⁻¹
      rw [_root_.mul_inv_rev]
      calc z * A * (h : GL (Fin n) K) * (A⁻¹ * z⁻¹) = z * (A * h * A⁻¹) * z⁻¹ := by group
        _ = (A * h * A⁻¹) * z * z⁻¹ := by rw [hc (A * h * A⁻¹)]
        _ = A * h * A⁻¹ := by group

end UnitaryConj

section Rev

theorem isJUnitary_conj_inv {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ} {P C : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hC : IsIdUnitary σ C) : IsJUnitary σ (P⁻¹ * C * P) := by
  unfold IsJUnitary
  unfold IsIdUnitary at hC
  rw [Units.val_mul, Units.val_mul]
  calc conjTr σ (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (C : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F)) * antidiag n *
        (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (C : Matrix (Fin n) (Fin n) F) *
          (P : Matrix (Fin n) (Fin n) F))
      = conjTr σ (P : Matrix (Fin n) (Fin n) F) * (conjTr σ (C : Matrix (Fin n) (Fin n) F) *
          (conjTr σ ((P : Matrix (Fin n) (Fin n) F) *
            ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
            ((P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))) *
          (C : Matrix (Fin n) (Fin n) F)) * (P : Matrix (Fin n) (Fin n) F) := by
        rw [← hP]
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = antidiag n := by
        rw [val_mul_val_inv, conjTr_one, Matrix.one_mul, Matrix.mul_one, hC, Matrix.mul_one, hP]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (τ : F ≃+* K)
  {n : ℕ} (P : GL (Fin n) F)
  (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
    (P : Matrix (Fin n) (Fin n) F) = antidiag n)

omit [Finite F] [CharP F 2] [Finite K] [CharP K 2] in
theorem isIdUnitary_glMap_symm [Finite F] [CharP F 2] [Finite K] [CharP K 2] {B : GL (Fin n) K}
    (hB : IsIdUnitary (unitaryInvolution K 2 f) B) :
    IsIdUnitary (unitaryInvolution F 2 f) ((glMap τ).symm B) := by
  unfold IsIdUnitary at hB ⊢
  rw [coe_glMap_symm, conjTr_map τ.symm (unitaryInvolution_map τ.symm), ← Matrix.map_mul, hB]
  exact Matrix.map_one _ (map_zero τ.symm) (map_one τ.symm)

theorem projConj_stdProj {B : GL (Fin n) K} (hB : IsIdUnitary (unitaryInvolution K 2 f) B)
    (hBN : B ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K (2 ^ f) : Set (GL (Fin n) K)))
    (u : SU (unitaryInvolution F 2 f) n) :
    TableB.projConj _ ⟨B, hBN⟩ (stdProj hK τ P hP u) =
      stdProj hK τ P hP (conjSU (P⁻¹ * (glMap τ).symm B * P)
        (isJUnitary_conj_inv hP (isIdUnitary_glMap_symm τ hB)) u) := by
  show TableB.projConj _ ⟨B, hBN⟩ ((suEquiv hK τ P hP u : LargeEvenSUGroup (Fin n) K (2 ^ f)) :
      LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f))) =
    ((suEquiv hK τ P hP (conjSU (P⁻¹ * (glMap τ).symm B * P)
        (isJUnitary_conj_inv hP (isIdUnitary_glMap_symm τ hB)) u) :
      LargeEvenSUGroup (Fin n) K (2 ^ f)) : LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)))
  rw [TableB.projConj_mk]
  congr 1
  apply Subtype.ext
  show B * (suEquiv hK τ P hP u : GL (Fin n) K) * B⁻¹ = (suEquiv hK τ P hP (conjSU _ _ u) :
    GL (Fin n) K)
  rw [coe_suEquiv, coe_suEquiv, coe_conjSU]
  have hC : glMap τ ((glMap τ).symm B) = B := (glMap τ).apply_symm_apply B
  calc B * glMap τ (P * (u : GL (Fin n) F) * P⁻¹) * B⁻¹
      = glMap τ ((glMap τ).symm B) * glMap τ (P * (u : GL (Fin n) F) * P⁻¹) *
          (glMap τ ((glMap τ).symm B))⁻¹ := by rw [hC]
    _ = glMap τ ((glMap τ).symm B * (P * (u : GL (Fin n) F) * P⁻¹) * ((glMap τ).symm B)⁻¹) := by
        simp only [map_mul, map_inv]
    _ = glMap τ (P * (P⁻¹ * (glMap τ).symm B * P * (u : GL (Fin n) F) *
          (P⁻¹ * (glMap τ).symm B * P)⁻¹) * P⁻¹) := by
        congr 1
        group

theorem ne_three_two {n : ℕ} (hn : 4 ≤ n) : (n, 2 ^ f) ≠ (3, 2) := fun h => by
  have := congrArg Prod.fst h
  simp only at this
  omega

include hF in
theorem ggRevProp_stdEquiv (hn : 4 ≤ n) {G : Type*} [Group G]
    (ψ : SU (unitaryInvolution F 2 f) n →* G) (hker : ψ.ker ≤ Subgroup.center _) :
    GGRevProp (rootDatum hF n) ψ ψ.range
      (ggInndiag (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)))
          (LargeEvenGUSet (Fin n) K (2 ^ f))))
      (stdEquiv hF hK τ P hP ψ (by omega) (ne_three_two hn) hker) := by
  rintro c hc ⟨φ, hφ, hind⟩
  obtain ⟨⟨B, hBN⟩, hB, rfl⟩ := ggInndiag_le_unitaryNorm hK hφ
  have hB' : IsIdUnitary (unitaryInvolution K 2 f) B := hB
  have hA := isJUnitary_conj_inv hP (isIdUnitary_glMap_symm τ hB')
  have hperf : commutator (SU (unitaryInvolution F 2 f) n) = ⊤ :=
    (isQuasisimple_SU hF (by omega) (ne_three_two hn)).1.commutator_eq_top
  have hmem : ∀ u, c⁻¹ * ψ u * c ∈ ψ.range := fun u => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) (ψ u)).mp ⟨u, rfl⟩
    rwa [inv_inv] at this
  let α : SU (unitaryInvolution F 2 f) n →* ↥ψ.range :=
    { toFun := fun u => ⟨c⁻¹ * ψ u * c, hmem u⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hα : ∀ u, ((α u : ↥ψ.range) : G) = c⁻¹ * ψ u * c := fun _ => rfl
  have hαβ : α = ψ.rangeRestrict.comp (conjSU _ hA) := by
    refine TypeA.eq_of_inv_mul_mem_center hperf _ _ fun u => ?_
    have h1 := hind (ψ.rangeRestrict u) (α u) (hα u)
    have h2 : stdEquiv hF hK τ P hP ψ (by omega) (ne_three_two hn) hker
        (QuotientGroup.mk (ψ.rangeRestrict (conjSU _ hA u))) =
        stdEquiv hF hK τ P hP ψ (by omega) (ne_three_two hn) hker (QuotientGroup.mk (α u)) := by
      rw [← h1]
      change stdEquiv hF hK τ P hP ψ _ _ hker (rangeProj ψ (conjSU _ hA u)) =
        TableB.projConj _ ⟨B, hBN⟩ (stdEquiv hF hK τ P hP ψ _ _ hker (rangeProj ψ u))
      rw [stdEquiv_rangeProj, stdEquiv_rangeProj, projConj_stdProj hK τ P hP hB' hBN]
    exact QuotientGroup.eq.mp ((stdEquiv hF hK τ P hP ψ _ _ hker).injective h2).symm
  have hconj : ∀ u, c⁻¹ * ψ u * c = ψ (conjSU _ hA u) := fun u => by
    rw [← hα, hαβ]
    rfl
  obtain ⟨d, hd, s, hs⟩ := exists_SU_mul_diag (by omega : 2 ≤ n) hA
  have hsD : ∀ z, s⁻¹ * conjSU _ hA z * s = conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z :=
    fun z => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSU, hs]
      group
  refine ⟨ψ s, ⟨s, rfl⟩, fun γ hγ => ?_⟩
  obtain ⟨h, hh, hzh⟩ := exists_torus_conj hF hn d hd hγ
  refine ⟨h, hh, fun z hz => ?_⟩
  calc (c * ψ s)⁻¹ * ψ z * (c * ψ s) = (ψ s)⁻¹ * (c⁻¹ * ψ z * c) * ψ s := by group
    _ = ψ (s⁻¹ * conjSU _ hA z * s) := by rw [hconj, map_mul, map_mul, map_inv]
    _ = ψ (h * z * h⁻¹) := by rw [hsD z, hzh z hz]

end Rev

section Exists

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem exists_stdEquiv_revProp (hn : 4 ≤ n) {G : Type} [Group G]
    (ψ : SU (unitaryInvolution F 2 f) n →* G) (hker : ψ.ker ≤ Subgroup.center _)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)),
      GGRevProp (rootDatum hF n) ψ ψ.range
        (ggInndiag (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)))
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)))
            (LargeEvenGUSet (Fin n) K (2 ^ f)))) θ₀ := by
  have : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, pow_mul])
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK]
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  exact ⟨_, ggRevProp_stdEquiv hF hK (FiniteField.ringEquivOfCardEq hcard) P hP hn ψ hker⟩

theorem stdUnitary_of_eq {G : Type} [Group G] {n f : ℕ} (hf : 1 ≤ f) (L : LieUniversal)
    (hL : L = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩)
    (ψ : L.K →* G) (hrk : 2 ≤ L.D.rank) (hker : ψ.ker ≤ Subgroup.center L.K)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)),
      GGRevProp L.D ψ ψ.range
        (ggInndiag (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)))
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)))
            (LargeEvenGUSet (Fin n) K (2 ^ f)))) θ₀ := by
  subst hL
  have hn : 4 ≤ n := by
    change 2 ≤ n / 2 at hrk
    omega
  exact exists_stdEquiv_revProp (card_galoisField_two_mul 2 f hf) hn ψ hker K hK

end Exists

end MpStdSU

section Input

theorem ggInnerDiagStdUnitary_holds : GGInnerDiagStdUnitary := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    intro ψ _ hrk _ hker K _ _ hK
    exact MpStdSU.stdUnitary_of_eq hf _ e ψ hrk hker K hK
  · intro ψ hadm
    exact absurd hadm.2.1 hf

end Input

section Families

theorem ggInnerDiagMpInputOn_unitary_holds : GGInnerDiagMpInputOn GGMpUnitaryLabel :=
  ggInnerDiagMpInputOn_unitary ggInnerDiagStdUnitary_holds

theorem ggInnerDiagMpInputOn_rest_of_stdExc (hE6 : GGInnerDiagStdE6)
    (h2E6 : GGInnerDiagStdTwE6) : GGInnerDiagMpInputOn fun lab => ¬ GGInnerDiagInnLabel lab :=
  ggInnerDiagMpInputOn_rest_of_std ggInnerDiagStdUnitary_holds hE6 h2E6

theorem ggInnerDiagMpInput_of_stdExc (hE6 : GGInnerDiagStdE6) (h2E6 : GGInnerDiagStdTwE6) :
    GGInnerDiagMpInput :=
  ggInnerDiagMpInput_of_std ggInnerDiagStdUnitary_holds hE6 h2E6

end Families

end CFSG.StandardType
