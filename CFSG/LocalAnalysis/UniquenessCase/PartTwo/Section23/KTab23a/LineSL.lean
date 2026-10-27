module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Open
open scoped Matrix

private def e0 (d : ℕ) [NeZero d] (K : Type) [Zero K] [One K] : Fin d → K :=
  Pi.single 0 1

private def fixedSubmodule (d : ℕ) [NeZero d] (K : Type) [Field K] :
    Submodule K (Fin d → K) :=
  LinearMap.ker (LinearMap.proj (R := K) (0 : Fin d))

private lemma mem_fixedSubmodule_iff {d : ℕ} [NeZero d] {K : Type} [Field K]
    (w : Fin d → K) : w ∈ fixedSubmodule d K ↔ w 0 = 0 := by
  simp [fixedSubmodule]

private lemma fixedSubmodule_coe_zero {d : ℕ} [NeZero d] {K : Type} [Field K]
    (w : fixedSubmodule d K) : w.val 0 = 0 :=
  (mem_fixedSubmodule_iff w.val).mp w.property

private lemma mkOfDetNeZero_coe {d : ℕ} {K : Type} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (h : A.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero A h : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = A := rfl

private lemma det_one_add_vecMulVec_single {d : ℕ} [NeZero d] {K : Type} [Field K]
    (w : Fin d → K) (hw : w 0 = 0) :
    (1 + Matrix.vecMulVec (e0 d K) w).det = 1 := by
  have h : Matrix.vecMulVec (e0 d K) w =
      Matrix.replicateCol Unit (e0 d K) * Matrix.replicateRow Unit w :=
    Matrix.vecMulVec_eq Unit _ _
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow, e0, dotProduct_single_one,
    hw, add_zero]

private lemma vecMulVec_single_mul_vecMulVec_single {d : ℕ} [NeZero d] {K : Type} [CommRing K]
    (w₁ w₂ : Fin d → K) (h₁ : w₁ 0 = 0) :
    Matrix.vecMulVec (e0 d K) w₁ * Matrix.vecMulVec (e0 d K) w₂ = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hdot : w₁ ⬝ᵥ (e0 d K) = 0 := by
    rw [e0, dotProduct_single_one, h₁]
  rw [hdot, zero_smul, Matrix.vecMulVec_zero]

private lemma one_add_vecMulVec_single_mul {d : ℕ} [NeZero d] {K : Type} [CommRing K]
    (w₁ w₂ : Fin d → K) (h₁ : w₁ 0 = 0) :
    (1 + Matrix.vecMulVec (e0 d K) w₁) * (1 + Matrix.vecMulVec (e0 d K) w₂) =
      1 + Matrix.vecMulVec (e0 d K) (w₁ + w₂) := by
  have hV : Matrix.vecMulVec (e0 d K) w₁ * Matrix.vecMulVec (e0 d K) w₂ = 0 :=
    vecMulVec_single_mul_vecMulVec_single w₁ w₂ h₁
  calc (1 + Matrix.vecMulVec (e0 d K) w₁) * (1 + Matrix.vecMulVec (e0 d K) w₂)
      = 1 + Matrix.vecMulVec (e0 d K) w₁ + Matrix.vecMulVec (e0 d K) w₂ +
          Matrix.vecMulVec (e0 d K) w₁ * Matrix.vecMulVec (e0 d K) w₂ := by
        noncomm_ring
    _ = 1 + Matrix.vecMulVec (e0 d K) w₁ + Matrix.vecMulVec (e0 d K) w₂ := by
        rw [hV, add_zero]
    _ = 1 + (Matrix.vecMulVec (e0 d K) w₁ + Matrix.vecMulVec (e0 d K) w₂) := by
        abel
    _ = 1 + Matrix.vecMulVec (e0 d K) (w₁ + w₂) := by
        rw [Matrix.vecMulVec_add]

private lemma vecMulVec_single_mulVec_eq_smul {d : ℕ} [NeZero d] {K : Type} [Field K]
    (w v : Fin d → K) :
    Matrix.vecMulVec (e0 d K) w *ᵥ v = (w ⬝ᵥ v) • (e0 d K) := by
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]

private lemma dotProduct_eq_zero_of_fixed {d : ℕ} [NeZero d] {K : Type} [Field K]
    {w v : Fin d → K} (h : (1 + Matrix.vecMulVec (e0 d K) w) *ᵥ v = v) :
    w ⬝ᵥ v = 0 := by
  have hV : Matrix.vecMulVec (e0 d K) w *ᵥ v = 0 := by
    have h' : v + Matrix.vecMulVec (e0 d K) w *ᵥ v = v + 0 := by
      rw [add_zero]
      simpa [Matrix.add_mulVec, Matrix.one_mulVec] using h
    exact add_left_cancel h'
  have h0 := congrFun hV 0
  rw [vecMulVec_single_mulVec_eq_smul] at h0
  simpa [e0] using h0

private noncomputable def rootElem (d : ℕ) [NeZero d] (K : Type) [Field K]
    (w : fixedSubmodule d K) : ↥(StatedSL d K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec (e0 d K) w.val)
      (by rw [det_one_add_vecMulVec_single w.val (fixedSubmodule_coe_zero w)];
          exact one_ne_zero),
   Subgroup.subset_closure (by
     simpa [mkOfDetNeZero_coe] using
       det_one_add_vecMulVec_single w.val (fixedSubmodule_coe_zero w))⟩

private noncomputable def rootHom (d : ℕ) [NeZero d] (K : Type) [Field K] :
    Multiplicative (fixedSubmodule d K) →* ↥(StatedSL d K) where
  toFun x := rootElem d K x.toAdd
  map_one' := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [rootElem, mkOfDetNeZero_coe]
  map_mul' x y := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, mkOfDetNeZero_coe, rootElem]
    rw [one_add_vecMulVec_single_mul x.toAdd.val y.toAdd.val (fixedSubmodule_coe_zero x.toAdd)]
    rfl

theorem exists_fixedLine_statedSL {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (d : ℕ) :
    ∃ (U : Subgroup ↥(StatedSL d K)) (e : Fin d → K), IsPGroup p ↥U ∧
      ∀ v : Fin d → K,
        (∀ u ∈ U, ((u : GL (Fin d) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} := by
  rcases d with _ | d
  · refine ⟨⊥, (0 : Fin 0 → K), IsPGroup.of_bot, ?_⟩
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  · refine ⟨(rootHom (d + 1) K).range, e0 (d + 1) K, ?_, ?_⟩
    · intro u
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp u.2
      have hxp : x ^ p = 1 := by
        apply Multiplicative.ext
        rw [toAdd_pow, toAdd_one]
        rw [← Nat.cast_smul_eq_nsmul K p x.toAdd, CharP.cast_eq_zero, zero_smul]
      refine ⟨1, ?_⟩
      rw [pow_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hx, ← map_pow, hxp, map_one]
      rfl
    · intro v hv
      have hcoord : ∀ i : Fin (d + 1), i ≠ 0 → v i = 0 := by
        intro i hi
        have hw : (Pi.single i (1 : K) : Fin (d + 1) → K) ∈ fixedSubmodule (d + 1) K := by
          rw [mem_fixedSubmodule_iff]
          simp [Pi.single_eq_of_ne' hi]
        have hmem : rootElem (d + 1) K ⟨Pi.single i (1 : K), hw⟩ ∈
            (rootHom (d + 1) K).range :=
          MonoidHom.mem_range.mpr
            ⟨Multiplicative.ofAdd ⟨Pi.single i (1 : K), hw⟩, rfl⟩
        have hfix := hv _ hmem
        have hmat : (1 + Matrix.vecMulVec (e0 (d + 1) K)
            (Pi.single i (1 : K) : Fin (d + 1) → K)) *ᵥ v = v := by
          simpa [rootHom, rootElem, e0, mkOfDetNeZero_coe] using hfix
        have hdot : (Pi.single i (1 : K) : Fin (d + 1) → K) ⬝ᵥ v = 0 :=
          dotProduct_eq_zero_of_fixed hmat
        rwa [single_one_dotProduct] at hdot
      have hv_eq : v = v 0 • (e0 (d + 1) K) := by
        ext i
        by_cases hi : i = 0
        · subst hi; simp [e0]
        · rw [hcoord i hi]
          simp [e0, Pi.single_eq_of_ne hi]
      rw [hv_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
