module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLLeviChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLBorelHall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open

variable {k : ℕ} {K : Type} [Field K]

private theorem slMat_pow_B04 (t : ↥(StatedSL k K)) (n : ℕ) :
    slMat (t ^ n) = (slMat t) ^ n :=
  map_pow ((Units.coeHom (Matrix (Fin k) (Fin k) K)).comp (StatedSL k K).subtype) t n

private theorem slMat_diag_mul_B04 [NeZero k] {t : ↥(StatedSL k K)} (hk1 : 1 < k)
    (hup : ∀ i j : Fin k, j < i → slMat t i j = 0)
    (hone : ∀ j : Fin k, 2 ≤ (j : ℕ) → slMat t j j = 1) :
    slMat t 0 0 * slMat t ⟨1, hk1⟩ ⟨1, hk1⟩ = 1 := by
  have hdet : (slMat t).det = 1 := by
    simpa [slMat] using CFSG.Open.StatedAPI.det_of_mem_statedSL (n := k) (K := K) t.2
  rw [Matrix.det_of_isUpperTriangular hup] at hdet
  have hprod : (∏ i : Fin k, slMat t i i)
      = slMat t 0 0 * slMat t ⟨1, hk1⟩ ⟨1, hk1⟩ :=
    Finset.prod_eq_mul (0 : Fin k) ⟨1, hk1⟩ (by
        intro h
        have : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
        omega)
      (fun c _ hc => hone c (by
        by_contra h
        have h2 : (c : ℕ) < 2 := Nat.lt_of_not_le h
        have hcases : (c : ℕ) = 0 ∨ (c : ℕ) = 1 := by omega
        rcases hcases with h0 | h1
        · exact hc.1 (Fin.ext (by simpa using h0))
        · exact hc.2 (Fin.ext (by simpa using h1))))
      (fun h => absurd (Finset.mem_univ _) h)
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hprod] at hdet
  exact hdet

theorem exists_conj_slTorusDiag [NeZero k] [Finite K] [CharP K 2] (hk : 2 ≤ k)
    {t : ↥(StatedSL k K)} (ht : t ∈ Hinf (slQAlpha k K) ⊓ slQZero k K)
    (hodd : Odd (orderOf t)) :
    ∃ s ∈ slU k K, ∃ c : K, c ≠ 0 ∧ slMat t 0 0 = c ∧
      slMat (s * t * s⁻¹) = Matrix.diagonal (slTorusDiag k c) := by
  have hk1 : 1 < k := by omega
  have htinf : t ∈ Hinf (slQAlpha k K) := ht.1
  have ht0 : t ∈ slQZero k K := ht.2
  have htQ : t ∈ slQAlpha k K :=
    Subgroup.map_subtype_le (CFSG.perfectResidual ↥(slQAlpha k K))
      (by simpa only [Hinf, CFSG.inSubgroup] using htinf)
  have hmem : t ∈ slQAlpha k K ⊓ slQZero k K := ⟨htQ, ht0⟩
  have hup : ∀ i j : Fin k, j < i → slMat t i j = 0 :=
    fun i j hij => slMat_lower_eq_zero_of_mem_inf hmem i j hij
  have hone : ∀ j : Fin k, 2 ≤ (j : ℕ) → slMat t j j = 1 :=
    fun j hj => slMat_diag_eq_one_of_mem_hinf htinf j hj
  obtain ⟨s, hsU, hsdiag⟩ := exists_conj_slU_diagonal hup hodd
  have hmain := slMat_diag_mul_B04 hk1 hup hone
  have hc_ne : slMat t 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmain
    exact zero_ne_one hmain
  have h11 : slMat t ⟨1, hk1⟩ ⟨1, hk1⟩ = (slMat t 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hmain
  refine ⟨s, hsU, slMat t 0 0, hc_ne, rfl, ?_⟩
  ext a b
  by_cases hab : a = b
  · rw [hab, Matrix.diagonal_apply_eq, slMat_conj_slU_apply_self hsU hup b]
    unfold slTorusDiag
    by_cases h0 : (b : ℕ) = 0
    · rw [if_pos h0]
      have hb0 : b = 0 := Fin.ext (by simpa using h0)
      subst hb0
      rfl
    · rw [if_neg h0]
      by_cases h1 : (b : ℕ) = 1
      · rw [if_pos h1]
        have hb1 : b = ⟨1, hk1⟩ := Fin.ext (by simpa using h1)
        subst hb1
        exact h11
      · rw [if_neg h1]
        exact hone b (by omega)
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact hsdiag a b hab

theorem orderOf_eq_of_slMat_eq_diagonal [NeZero k] {c : K} {t' : ↥(StatedSL k K)}
    (h : slMat t' = Matrix.diagonal (slTorusDiag k c)) : orderOf t' = orderOf c := by
  refine orderOf_eq_orderOf_iff.mpr ?_
  intro n
  have hpow : slMat (t' ^ n) = Matrix.diagonal (slTorusDiag k c ^ n) := by
    rw [slMat_pow_B04, h, Matrix.diagonal_pow]
  constructor
  · intro hn
    have h0 : slMat (t' ^ n) = (1 : Matrix (Fin k) (Fin k) K) := by
      rw [hn]
      simp [slMat]
    rw [hpow] at h0
    have h00 := congr_fun (congr_fun h0 0) 0
    rw [Matrix.diagonal_apply_eq, Pi.pow_apply] at h00
    simpa [slTorusDiag] using h00
  · intro hc
    apply Subtype.ext
    apply Units.ext
    show slMat (t' ^ n) = 1
    rw [hpow]
    ext a b
    by_cases hab : a = b
    · rw [hab, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.pow_apply]
      unfold slTorusDiag
      split_ifs <;> simp [hc, inv_pow]
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
