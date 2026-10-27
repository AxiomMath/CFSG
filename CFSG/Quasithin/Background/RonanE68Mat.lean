module

public import CFSG.Quasithin.Background.E6EightMarkedRoots
public import CFSG.Quasithin.Background.ONanE68Sp4Roots

public section

namespace CFSG.Quasithin.RonanE68

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.SteinbergBS CFSG.Quasithin.E6.E68Proof.Sp4
  CFSG.Open CFSG.Quasithin.E6

variable {K : Type} [Field K] [CharP K 2]

theorem statedSp_ext {g h : StatedSp 2 K} (H : spMat g = spMat h) : g = h :=
  Subtype.ext (Units.ext H)

theorem antiIdx_eq_zero_iff (a : Fin 2 ⊕ Fin 2) : (0 : Fin 4) = antiIdx a ↔ Sum.inl 0 = a := by
  rw [show (0 : Fin 4) = antiIdx (Sum.inl 0) from rfl]
  exact antiIdx.injective.eq_iff

theorem antiIdx_eq_one_iff (a : Fin 2 ⊕ Fin 2) : (1 : Fin 4) = antiIdx a ↔ Sum.inl 1 = a := by
  rw [show (1 : Fin 4) = antiIdx (Sum.inl 1) from rfl]
  exact antiIdx.injective.eq_iff

theorem antiIdx_eq_two_iff (a : Fin 2 ⊕ Fin 2) : (2 : Fin 4) = antiIdx a ↔ Sum.inr 1 = a := by
  rw [show (2 : Fin 4) = antiIdx (Sum.inr 1) from rfl]
  exact antiIdx.injective.eq_iff

theorem antiIdx_eq_three_iff (a : Fin 2 ⊕ Fin 2) : (3 : Fin 4) = antiIdx a ↔ Sum.inr 0 = a := by
  rw [show (3 : Fin 4) = antiIdx (Sum.inr 0) from rfl]
  exact antiIdx.injective.eq_iff

theorem longMat_eq [Finite K] (t : K) :
    (glMat (uElt (0 : K) 0 t 0 : GL (Fin 4) K)).submatrix antiIdx antiIdx =
      Matrix.of fun row col : Fin 2 ⊕ Fin 2 => (if row = col then 1 else 0) +
        (if row = Sum.inl 0 ∧ col = Sum.inr 0 then t else 0) := by
  ext a b
  simp only [Matrix.submatrix_apply, glMat_uElt_long, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.of_apply, antiIdx.injective.eq_iff, antiIdx_eq_zero_iff,
    antiIdx_eq_three_iff]
  simp only [eq_comm]

theorem map_rootLong_antiSpEquiv [Finite K] :
    (rootLong K).map (antiSpEquiv K).toMonoidHom = sp4LongRoot K := by
  apply le_antisymm
  · rintro _ ⟨g, ⟨t, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨t, ?_⟩
    exact longMat_eq t
  · rw [sp4LongRoot, Subgroup.closure_le]
    rintro g ⟨t, hg⟩
    refine ⟨uElt 0 0 t 0, ⟨t, rfl⟩, ?_⟩
    apply statedSp_ext
    have hg' : spMat g = Matrix.of fun row col : Fin 2 ⊕ Fin 2 =>
        (if row = col then 1 else 0) + (if row = Sum.inl 0 ∧ col = Sum.inr 0 then t else 0) := hg
    rw [hg']
    exact (spMat_antiSpEquiv (uElt (0 : K) 0 t 0)).trans (longMat_eq t)

open CFSG.RankThree.PartOne.KCRootAxis (mat mat_mul mat_one mat_ext)

theorem pElt2_inv [Finite K] : (pElt2 : antiSp K)⁻¹ = pElt2 :=
  inv_eq_of_mul_eq_one_right (mat_ext (by rw [mat_mul, mat_pElt2, pMat2_mul_self, mat_one]))

theorem mat_conj_short [Finite K] (t : K) :
    mat ((pElt2 : antiSp K)⁻¹ * uElt (0 : K) t 0 0 * pElt2) =
      1 + t • (Matrix.single 0 1 (1 : K) + Matrix.single 2 3 (1 : K)) := by
  rw [pElt2_inv, mat_mul, mat_mul, mat_pElt2, mat_uElt_short]
  have h1 : (pMat2 : Matrix (Fin 4) (Fin 4) K) * nShort * pMat2 =
      Matrix.single 0 1 (1 : K) + Matrix.single 2 3 (1 : K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pMat2, nShort, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply]
  calc (pMat2 : Matrix (Fin 4) (Fin 4) K) * (1 + t • nShort) * pMat2
      = pMat2 * pMat2 + t • (pMat2 * nShort * pMat2) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    _ = 1 + t • (Matrix.single 0 1 (1 : K) + Matrix.single 2 3 (1 : K)) := by
        rw [pMat2_mul_self, h1]

theorem shortMat_eq [Finite K] (t : K) :
    (mat ((pElt2 : antiSp K)⁻¹ * uElt (0 : K) t 0 0 * pElt2)).submatrix antiIdx antiIdx =
      Matrix.of fun row col : Fin 2 ⊕ Fin 2 => (if row = col then 1 else 0) +
        (if row = Sum.inl 0 ∧ col = Sum.inl 1 then t else 0) -
        (if row = Sum.inr 1 ∧ col = Sum.inr 0 then t else 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [mat_conj_short]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.single_apply, Matrix.one_apply, antiIdx_inl_zero, antiIdx_inl_one,
      antiIdx_inr_zero, antiIdx_inr_one] <;>
    first | done | linear_combination t * h2 | linear_combination (-t) * h2

theorem map_rootShort_antiSpEquiv [Finite K] :
    (rootShort K).map (antiSpEquiv K).toMonoidHom =
      (sp4ShortRoot K).map (MulAut.conj (antiSpEquiv K (pElt2 : antiSp K))).toMonoidHom := by
  have hgen : ∀ t : K, antiSpEquiv K ((pElt2 : antiSp K)⁻¹ * uElt (0 : K) t 0 0 * pElt2) ∈
      {element : ↥(CFSG.Open.StatedSp 2 K) | ∃ parameter : K,
        ((element : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          Matrix.of fun row column => (if row = column then 1 else 0) +
            (if row = Sum.inl 0 ∧ column = Sum.inl 1 then parameter else 0) -
            (if row = Sum.inr 1 ∧ column = Sum.inr 0 then parameter else 0)} := fun t =>
    ⟨t, (spMat_antiSpEquiv _).trans (shortMat_eq t)⟩
  have hconj : ∀ t : K, (MulAut.conj (antiSpEquiv K (pElt2 : antiSp K))).toMonoidHom
      (antiSpEquiv K ((pElt2 : antiSp K)⁻¹ * uElt (0 : K) t 0 0 * pElt2)) =
        antiSpEquiv K (uElt (0 : K) t 0 0) := fun t => by
    show antiSpEquiv K pElt2 * antiSpEquiv K ((pElt2 : antiSp K)⁻¹ * uElt (0 : K) t 0 0 * pElt2) *
      (antiSpEquiv K pElt2)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  apply le_antisymm
  · rintro _ ⟨g, ⟨t, rfl⟩, rfl⟩
    refine ⟨_, Subgroup.subset_closure (hgen t), hconj t⟩
  · rw [Subgroup.map_le_iff_le_comap, sp4ShortRoot, Subgroup.closure_le]
    rintro s ⟨t, hs⟩
    have hseq : s = antiSpEquiv K ((pElt2 : antiSp K)⁻¹ * uElt (0 : K) t 0 0 * pElt2) := by
      apply statedSp_ext
      rw [(spMat_antiSpEquiv _).trans (shortMat_eq t)]
      exact hs
    refine Subgroup.mem_comap.2 ?_
    rw [hseq, hconj t]
    exact ⟨uElt (0 : K) t 0 0, ⟨t, rfl⟩, rfl⟩

end CFSG.Quasithin.RonanE68
