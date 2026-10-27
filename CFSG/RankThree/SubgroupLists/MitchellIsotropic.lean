module

public import CFSG.RankThree.SubgroupLists.MitchellDegenerate
public import CFSG.RankThree.SubgroupLists.SymplecticHeisenberg
public import CFSG.RankThree.SubgroupLists.SymplecticRegulus

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def isoStd : Matrix V₄ V₄ K := cliffMat 0 0 0 1 0

@[expose] def matCent (Z : Matrix V₄ V₄ K) : Subgroup (GL V₄ K) where
  carrier := {g | (g : Matrix V₄ V₄ K) * Z = Z * (g : Matrix V₄ V₄ K)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (a : Matrix V₄ V₄ K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h1' : (a : Matrix V₄ V₄ K) * ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * Z
        = ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * Z * ((a : Matrix V₄ V₄ K) *
            ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by rw [h1', Matrix.mul_one]
      _ = ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (Z * (a : Matrix V₄ V₄ K)) *
            ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by simp only [Matrix.mul_assoc]
      _ = ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((a : Matrix V₄ V₄ K) * Z) *
            ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by rw [ha]
      _ = Z * ((a⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_matCent {Z : Matrix V₄ V₄ K} {g : GL V₄ K} :
    g ∈ matCent Z ↔ (g : Matrix V₄ V₄ K) * Z = Z * (g : Matrix V₄ V₄ K) := Iff.rfl

@[expose] def isoCent (K : Type) [Field K] : Subgroup (GL V₄ K) :=
  StatedSp 2 K ⊓ matCent isoStd

@[expose] def leviBlock (M : Matrix V₄ V₄ K) : Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl 0) (Sum.inl 0), M (Sum.inl 0) (Sum.inl 1);
    M (Sum.inl 1) (Sum.inl 0), M (Sum.inl 1) (Sum.inl 1)]

theorem entries_of_commute_isoStd {g : Matrix V₄ V₄ K} (hg : g * isoStd = isoStd * g) :
    (∀ i j : Fin 2, g (Sum.inr i) (Sum.inl j) = 0) ∧
      g (Sum.inr 1) (Sum.inr 0) = -g (Sum.inl 0) (Sum.inl 1) ∧
      g (Sum.inr 0) (Sum.inr 0) = g (Sum.inl 1) (Sum.inl 1) ∧
      g (Sum.inr 1) (Sum.inr 1) = g (Sum.inl 0) (Sum.inl 0) ∧
      g (Sum.inr 0) (Sum.inr 1) = -g (Sum.inl 1) (Sum.inl 0) := by
  have e : ∀ a b : V₄, (g * isoStd : Matrix V₄ V₄ K) a b = (isoStd * g : Matrix V₄ V₄ K) a b :=
    fun a b => by rw [hg]
  have e1 := e (Sum.inl 0) (Sum.inl 0)
  have e2 := e (Sum.inl 0) (Sum.inl 1)
  have e3 := e (Sum.inl 1) (Sum.inl 0)
  have e4 := e (Sum.inl 1) (Sum.inl 1)
  have e5 := e (Sum.inl 0) (Sum.inr 0)
  have e6 := e (Sum.inl 1) (Sum.inr 0)
  have e7 := e (Sum.inl 0) (Sum.inr 1)
  have e8 := e (Sum.inl 1) (Sum.inr 1)
  simp [isoStd, cliffMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at e1 e2 e3 e4
  simp [isoStd, cliffMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at e5 e6 e7 e8
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  · linear_combination -e5
  · linear_combination -e6
  · linear_combination -e7
  · linear_combination e8

theorem leviBlock_mul {g h : Matrix V₄ V₄ K} (hh : ∀ i j : Fin 2, h (Sum.inr i) (Sum.inl j) = 0) :
    leviBlock (g * h) = leviBlock g * leviBlock h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hh]

theorem leviBlock_one : leviBlock (1 : Matrix V₄ V₄ K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviBlock, Matrix.one_apply]

theorem det_leviBlock {g : GL V₄ K} (hg : g ∈ isoCent K) : (leviBlock (g : Matrix V₄ V₄ K)).det =
    1 := by
  obtain ⟨hl, h1, h2, -, -⟩ := entries_of_commute_isoStd hg.2
  have h := spGram_entry hg.1 (Sum.inl 0) (Sum.inr 0)
  simp only [Fin.sum_univ_two, hl, zero_mul, sub_zero, h1, h2] at h
  rw [leviBlock, Matrix.det_fin_two_of]
  simp [spGram, Matrix.fromBlocks] at h
  linear_combination h

@[expose] noncomputable def leviHom (K : Type) [Field K] : isoCent K →* SL(2, K) where
  toFun g := ⟨leviBlock ((g : GL V₄ K) : Matrix V₄ V₄ K), det_leviBlock g.2⟩
  map_one' := by
    apply Subtype.ext
    exact leviBlock_one
  map_mul' g h := by
    apply Subtype.ext
    change leviBlock (((g : GL V₄ K) : Matrix V₄ V₄ K) * ((h : GL V₄ K) : Matrix V₄ V₄ K)) =
      leviBlock ((g : GL V₄ K) : Matrix V₄ V₄ K) * leviBlock ((h : GL V₄ K) : Matrix V₄ V₄ K)
    exact leviBlock_mul (entries_of_commute_isoStd h.2.2).1

theorem coe_leviHom (g : isoCent K) :
    ((leviHom K g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      leviBlock ((g : GL V₄ K) : Matrix V₄ V₄ K) := rfl

theorem isSqZero_of_leviBlock_eq_one {g : GL V₄ K} (hg : g ∈ isoCent K)
    (h1 : leviBlock (g : Matrix V₄ V₄ K) = 1) : IsSqZero g := by
  obtain ⟨hl, e1, e2, e3, e4⟩ := entries_of_commute_isoStd hg.2
  have h00 : (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) = 1 := by
    simpa [leviBlock] using congrFun (congrFun h1 0) 0
  have h01 : (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1) = 0 := by
    simpa [leviBlock] using congrFun (congrFun h1 0) 1
  have h10 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 0) = 0 := by
    simpa [leviBlock] using congrFun (congrFun h1 1) 0
  have h11 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 1) = 1 := by
    simpa [leviBlock] using congrFun (congrFun h1 1) 1
  rw [h01] at e1
  rw [h11] at e2
  rw [h00] at e3
  rw [h10] at e4
  have l00 := hl 0 0
  have l01 := hl 0 1
  have l10 := hl 1 0
  have l11 := hl 1 1
  unfold IsSqZero
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply, h00, h01,
      h10, h11, e1, e2, e3, e4, l00, l01, l10, l11]

section Normalise

variable (h2 : (2 : K) ≠ 0)
include h2

omit h2 in
theorem spForm_mulVec_eq_zero {X : Matrix V₄ V₄ K} (hX : Xᵀ * spGram 2 K * X = 0)
    (x y : V₄ → K) : spForm 2 K (X *ᵥ x) (X *ᵥ y) = 0 := by
  rw [spForm_eq_dotProduct, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hX,
    Matrix.zero_mulVec, dotProduct_zero]

theorem mul_self_eq_zero_of_isotropic {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrr : cliffB r r = 0) : r * r = 0 := by
  rw [mul_self_of_mem h2 hrM, ← cliffB_self h2, hrr, zero_smul]

theorem exists_nonisotropic_cliffB_ne_zero {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrr : cliffB r r = 0) (hr0 : r ≠ 0) :
    ∃ u ∈ (cliffSpace : Submodule K _), cliffB u u ≠ 0 ∧ cliffB u r ≠ 0 := by
  obtain ⟨s, hsM, hsr⟩ : ∃ s ∈ (cliffSpace : Submodule K _), cliffB s r ≠ 0 := by
    by_contra h
    push Not at h
    exact hr0 (eq_zero_of_cliffB_eq_zero h2 hrM fun Y hY => by rw [cliffB_comm]; exact h Y hY)
  by_cases hs : cliffB s s = 0
  · refine ⟨s + r, Submodule.add_mem _ hsM hrM, ?_, ?_⟩
    · rw [cliffQ_add_eq, hs, hrr]
      intro h
      apply hsr
      have : (2 : K) * cliffB s r = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h2
    · rw [cliffB_add_left, hrr, add_zero]
      exact hsr
  · exact ⟨s, hsM, hs, hsr⟩

theorem exists_lagrangian_pair {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrr : cliffB r r = 0) (hr0 : r ≠ 0) :
    ∃ B : Submodule K (V₄ → K),
      finrank K (LinearMap.range (Matrix.toLin' r)) = 2 ∧ finrank K B = 2 ∧
      (∀ x ∈ LinearMap.range (Matrix.toLin' r), ∀ y ∈ LinearMap.range (Matrix.toLin' r),
        spForm 2 K x y = 0) ∧ (∀ x ∈ B, ∀ y ∈ B, spForm 2 K x y = 0) ∧
      LinearMap.range (Matrix.toLin' r) ⊓ B = ⊥ := by
  classical
  obtain ⟨u, huM, hQu, hur⟩ := exists_nonisotropic_cliffB_ne_zero h2 hrM hrr hr0
  have hrr0 := mul_self_eq_zero_of_isotropic h2 hrM hrr
  set A := LinearMap.range (Matrix.toLin' r) with hA
  set B := LinearMap.range (Matrix.toLin' (u * r)) with hB
  have hJr : rᵀ * spGram 2 K = spGram 2 K * r := hrM.1
  have hJu : uᵀ * spGram 2 K = spGram 2 K * u := huM.1
  have huu : u * u = cliffB u u • (1 : Matrix V₄ V₄ K) := by
    rw [mul_self_of_mem h2 huM, cliffB_self h2]
  have hAker : A ≤ LinearMap.ker (Matrix.toLin' r) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hrr0,
      Matrix.zero_mulVec]
  have hdim4 : finrank K (V₄ → K) = 4 := by simp
  have hrk : finrank K A + finrank K (LinearMap.ker (Matrix.toLin' r)) = 4 := by
    rw [hA, LinearMap.finrank_range_add_finrank_ker, hdim4]
  have hA2 : finrank K A ≤ 2 := by
    have := Submodule.finrank_mono hAker
    omega
  have hBA : finrank K B ≤ finrank K A := by
    have : B = A.map (Matrix.toLin' u) := by
      rw [hB, hA, Matrix.toLin'_mul, LinearMap.range_comp]
    rw [this]
    exact Submodule.finrank_map_le _ _
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hc : (2 * cliffB u r) ≠ 0 := mul_ne_zero h2 hur
    have hsum := mul_add_mul_of_mem h2 huM hrM
    have hv : v = (2 * cliffB u r)⁻¹ • (r *ᵥ (u *ᵥ v)) +
        (2 * cliffB u r)⁻¹ • ((u * r) *ᵥ v) := by
      rw [← smul_add, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, add_comm (r * u), hsum,
        Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hv]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ ?_))
    · exact ⟨u *ᵥ v, by rw [Matrix.toLin'_apply]⟩
    · exact ⟨v, by rw [Matrix.toLin'_apply]⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top, hdim4] at hsum
  have hAeq : finrank K A = 2 := by omega
  have hBeq : finrank K B = 2 := by omega
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    omega
  refine ⟨B, hAeq, hBeq, ?_, ?_, hinf⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    refine spForm_mulVec_eq_zero ?_ x y
    rw [hJr, Matrix.mul_assoc, hrr0, Matrix.mul_zero]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    refine spForm_mulVec_eq_zero ?_ x y
    calc (u * r)ᵀ * spGram 2 K * (u * r) = rᵀ * (uᵀ * spGram 2 K) * u * r := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = rᵀ * spGram 2 K * (u * u) * r := by rw [hJu]; simp only [Matrix.mul_assoc]
      _ = cliffB u u • (rᵀ * spGram 2 K * r) := by
          rw [huu, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = 0 := by rw [hJr, Matrix.mul_assoc, hrr0, Matrix.mul_zero, smul_zero]

theorem exists_conj_eq_smul_isoStd {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrr : cliffB r r = 0) (hr0 : r ≠ 0) :
    ∃ h ∈ StatedSp 2 K, ∃ b : K, b ≠ 0 ∧
      ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * r * (h : Matrix V₄ V₄ K) = b • isoStd := by
  classical
  obtain ⟨B, hA2, hB2, hAiso, hBiso, hAB⟩ := exists_lagrangian_pair h2 hrM hrr hr0
  obtain ⟨h, hhS, hhA, -⟩ := exists_mem_statedSp_translate_eq hA2 hB2 hAiso hBiso hAB
  refine ⟨h, hhS, ?_⟩
  set R : Matrix V₄ V₄ K := ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * r * (h : Matrix V₄ V₄ K) with hRdef
  have hhh : ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (h : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrow : ∀ (i : Fin 2) (j : V₄), R (Sum.inr i) j = 0 := by
    intro i j
    have hmem : r *ᵥ ((h : Matrix V₄ V₄ K) *ᵥ Pi.single j 1) ∈ translate h lagInl := by
      rw [hhA]
      exact ⟨_, by rw [Matrix.toLin'_apply]⟩
    obtain ⟨w, hw, hwe⟩ := mem_translate.mp hmem
    have hRj : R *ᵥ Pi.single j 1 = w := by
      rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hwe, Matrix.mulVec_mulVec,
        hhh, Matrix.one_mulVec]
    calc R (Sum.inr i) j = (R *ᵥ Pi.single j 1) (Sum.inr i) := by
          simp [Matrix.mulVec_single_one]
      _ = w (Sum.inr i) := by rw [hRj]
      _ = 0 := hw i
  have hRM : R ∈ (cliffSpace : Submodule K _) := by
    have := conj_mem_cliffSpace (g := h⁻¹) (inv_mem hhS) hrM
    rwa [inv_inv] at this
  have hR := eq_cliffMat_of_mem h2 hRM
  have entry : ∀ a b : V₄, R a b = (cliffMat (R (Sum.inl 0) (Sum.inl 0)) (R (Sum.inl 0) (Sum.inl 1))
      (R (Sum.inl 1) (Sum.inl 0)) (R (Sum.inl 0) (Sum.inr 1)) (R (Sum.inr 0) (Sum.inl 1))) a b :=
    fun a b => congrFun (congrFun hR a) b
  have hx : R (Sum.inl 0) (Sum.inl 0) = 0 := by
    have := entry (Sum.inr 0) (Sum.inr 0)
    rw [hrow] at this
    simpa [cliffMat] using this.symm
  have hy : R (Sum.inl 0) (Sum.inl 1) = 0 := by
    have := entry (Sum.inr 1) (Sum.inr 0)
    rw [hrow] at this
    simpa [cliffMat] using this.symm
  have hz : R (Sum.inl 1) (Sum.inl 0) = 0 := by
    have := entry (Sum.inr 0) (Sum.inr 1)
    rw [hrow] at this
    simpa [cliffMat] using this.symm
  have hc : R (Sum.inr 0) (Sum.inl 1) = 0 := hrow 0 _
  refine ⟨R (Sum.inl 0) (Sum.inr 1), ?_, ?_⟩
  · intro hb
    apply hr0
    have hR0 : R = 0 := by rw [hR, hx, hy, hz, hb, hc]; exact cliffMat_zero
    calc r = (h : Matrix V₄ V₄ K) * R * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
          rw [hRdef]
          simp only [← Matrix.mul_assoc]
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
            ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = 0 := by rw [hR0, Matrix.mul_zero, Matrix.zero_mul]
  · calc R = cliffMat (R (Sum.inl 0) (Sum.inl 0)) (R (Sum.inl 0) (Sum.inl 1))
          (R (Sum.inl 1) (Sum.inl 0)) (R (Sum.inl 0) (Sum.inr 1)) (R (Sum.inr 0) (Sum.inl 1)) := hR
      _ = R (Sum.inl 0) (Sum.inr 1) • isoStd := by
          rw [hx, hy, hz, hc]
          ext a b
          rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
            simp [isoStd, cliffMat]

end Normalise

end CFSG.RankThree.SubgroupLists
