module

public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.PartOne.KE.E7TwelveLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open scoped Matrix Polynomial

theorem e7T12Cols_image_lt_three :
    e7T12Cols '' {i : Fin Tag.E7.rank | (i : ℕ) < 3} = {e7T12Alpha, e7T12Beta, e7T12Gamma} := by
  ext u
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi3 : (i : ℕ) < 3 := hi
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 by omega) with h | h | h
    · simp [e7T12Cols, h]
    · simp [e7T12Cols, h]
    · simp [e7T12Cols, h]
  · intro hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, by simp, by simp [e7T12Cols]⟩
    · exact ⟨⟨1, by decide⟩, by simp, by simp [e7T12Cols]⟩
    · exact ⟨⟨2, by decide⟩, by simp, by simp [e7T12Cols]⟩

open Polynomial in
theorem e7Twelve_block_cyclic {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    IsCyclic (fixedBlockTuples e7T12W Fr {e7T12Alpha, e7T12Beta, e7T12Gamma}) ∧
      Nat.card (fixedBlockTuples e7T12W Fr {e7T12Alpha, e7T12Beta, e7T12Gamma}) =
        q ^ 4 - q ^ 2 + 1 := by
  obtain ⟨hWα, hWβ, hWγ⟩ := e7T12W_cycle
  have hmem : ∀ u ∈ ({e7T12Alpha, e7T12Beta, e7T12Gamma} : Set (Fin Tag.E7.rank → ℤ)),
      u ∈ Submodule.span ℤ (e7T12Cols '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := fun u hu => by
    rw [e7T12Cols_image_lt_three]
    exact Submodule.subset_span hu
  have hPmonic : (X ^ 4 - X ^ 2 + 1 : ℤ[X]).Monic := by
    have h : (X ^ 4 - X ^ 2 + 1 : ℤ[X]) = X ^ 4 + (-X ^ 2 + 1) := by ring
    rw [h]
    refine Polynomial.monic_X_pow_add ?_
    have : (-X ^ 2 + 1 : ℤ[X]).degree ≤ 2 := by
      refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
      · rw [Polynomial.degree_neg]
        exact (Polynomial.degree_X_pow_le 2)
      · exact (Polynomial.degree_one_le).trans (by norm_num)
    exact lt_of_le_of_lt this (by norm_num)
  have hPdeg : (X ^ 4 - X ^ 2 + 1 : ℤ[X]).natDegree = Tag.E7.rank - 3 := by
    have h : (X ^ 4 - X ^ 2 + 1 : ℤ[X]).natDegree = 4 := by
      compute_degree!
    rw [h]
    rfl
  have hcoeff : (X ^ 4 - X ^ 2 + 1 : ℤ[X]).coeff 0 = 1 := by
    simp [Polynomial.coeff_one]
  have hne : (X ^ 4 - X ^ 2 + 1 : ℤ[X]).eval (q : ℤ) ≠ 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    intro h0
    nlinarith [sq_nonneg (2 * (q : ℤ) ^ 2 - 1)]
  have h := isCyclic_and_card_fixedBlockTuples (L := L) e7T12W e7T12Cols (k := 3) (by decide)
    e7T12V e7T12Cols_basis.1 e7T12Cols_basis.2
    (fun j hj => by
      have h0 : (j : ℕ) ≠ 0 := by omega
      have h1 : (j : ℕ) ≠ 1 := by omega
      have h2 : (j : ℕ) ≠ 2 := by omega
      simp [e7T12Cols, h0, h1, h2])
    (fun j hj => by
      have hj3 : (j : ℕ) < 3 := hj
      rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 by omega) with h | h | h
      · have : e7T12Cols j = e7T12Alpha := by simp [e7T12Cols, h]
        rw [this, hWα]
        exact hmem _ (by simp)
      · have : e7T12Cols j = e7T12Beta := by simp [e7T12Cols, h]
        rw [this, hWβ]
        exact hmem _ (by simp)
      · have : e7T12Cols j = e7T12Gamma := by simp [e7T12Cols, h]
        rw [this, hWγ]
        exact hmem _ (by simp))
    (X ^ 4 - X ^ 2 + 1) hPmonic hPdeg
    (by
      have h1 : (Polynomial.aeval e7T12W (X ^ 4 - X ^ 2 + 1 : ℤ[X])) *ᵥ e7T12V =
          e7T12Gamma - e7T12Alpha := by
        rw [← e7T12_relation]
        simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, map_one, Matrix.add_mulVec,
          Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [h1]
      exact Submodule.sub_mem _ (hmem _ (by simp)) (hmem _ (by simp)))
    Fr hFr hℓ hℓq (Or.inl hcoeff) hne
  rw [e7T12Cols_image_lt_three] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one]
  have h24 : q ^ 2 ≤ q ^ 4 := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      norm_num
    · exact Nat.pow_le_pow_right h0 (by norm_num)
  have e : (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 = ((q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h24]
    ring
  rw [e, Int.natAbs_natCast]

theorem e7Twelve_rootCharKernel {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : orderOf (q : ZMod p) = 12) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e7T12W Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a =
      {e7T12Alpha, -e7T12Alpha, e7T12Beta, -e7T12Beta, e7T12Gamma, -e7T12Gamma} := by
  obtain ⟨z, hz0, hzM, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples e7T12W Fr hFr hp ha hap ha1
  have : Fact p.Prime := ⟨hp⟩
  rw [hzk]
  exact e7T12_root_kernel p hp2 (q : ZMod p) hq z hz0 hzM

end CFSG.RankThree.PartOne.KE
