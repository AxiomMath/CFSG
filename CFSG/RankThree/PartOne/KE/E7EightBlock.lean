module

public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.Lattice.SteinbergBIE7OrderEight

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open scoped Matrix Polynomial

@[expose] def e7EightCols : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ := fun j =>
  if (j : ℕ) = 0 then e7O8Alpha else if (j : ℕ) = 1 then e7O8Beta
  else if (j : ℕ) = 2 then e7O8Gamma else (e7O8W ^ ((j : ℕ) - 3)) *ᵥ e7O8V

theorem e7EightCols_basis :
    LinearIndependent ℤ e7EightCols ∧ Submodule.span ℤ (Set.range e7EightCols) = ⊤ := by
  obtain ⟨-, -, ⟨-, hspan0⟩, -, -, -, -, -, hβdef, hγdef, -⟩ :=
    E7_order_eight_lattice_and_exact_three_A1_prime_root_kernel
  set Sp := Submodule.span ℤ (Set.range e7EightCols) with hSp
  have hα : e7O8Alpha ∈ Sp :=
    Submodule.subset_span ⟨⟨0, by decide⟩, by simp [e7EightCols]⟩
  have hβ : e7O8Beta ∈ Sp :=
    Submodule.subset_span ⟨⟨1, by decide⟩, by simp [e7EightCols]⟩
  have hγ : e7O8Gamma ∈ Sp :=
    Submodule.subset_span ⟨⟨2, by decide⟩, by simp [e7EightCols]⟩
  have hV : e7O8V ∈ Sp :=
    Submodule.subset_span ⟨⟨3, by decide⟩, by simp [e7EightCols]⟩
  have hWV : (e7O8W ^ 1) *ᵥ e7O8V ∈ Sp :=
    Submodule.subset_span ⟨⟨4, by decide⟩, by simp [e7EightCols]⟩
  have hW2V : (e7O8W ^ 2) *ᵥ e7O8V ∈ Sp :=
    Submodule.subset_span ⟨⟨5, by decide⟩, by simp [e7EightCols]⟩
  have hW3V : (e7O8W ^ 3) *ᵥ e7O8V ∈ Sp :=
    Submodule.subset_span ⟨⟨6, by decide⟩, by simp [e7EightCols]⟩
  have hW4V : (e7O8W ^ 4) *ᵥ e7O8V ∈ Sp := by
    have : (e7O8W ^ 4) *ᵥ e7O8V = e7O8Beta - e7O8V - e7O8Alpha := by
      rw [hβdef]
      abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hβ hV) hα
  have hW5V : (e7O8W ^ 5) *ᵥ e7O8V ∈ Sp := by
    have : (e7O8W ^ 5) *ᵥ e7O8V = e7O8Gamma - (e7O8W ^ 1) *ᵥ e7O8V - e7O8Alpha := by
      rw [hγdef, pow_one]
      abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hγ hWV) hα
  have hall : ∀ j : Fin Tag.E7.rank, e7O8Cols j ∈ Sp := by
    intro j
    by_cases hj : (j : ℕ) < 6
    · have h : e7O8Cols j = (e7O8W ^ (j : ℕ)) *ᵥ e7O8V := by simp [e7O8Cols, hj]
      rw [h]
      have hj6 : (j : ℕ) < 6 := hj
      interval_cases hjj : (j : ℕ)
      · simpa using hV
      · exact hWV
      · exact hW2V
      · exact hW3V
      · exact hW4V
      · exact hW5V
    · have h : e7O8Cols j = e7O8Alpha := by simp [e7O8Cols, hj]
      rw [h]
      exact hα
  have hspan : Sp = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hspan0]
    exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hall j)
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge ?_, hspan⟩
  rw [Module.finrank_fintype_fun_eq_card]

theorem e7EightCols_image_lt_three :
    e7EightCols '' {i : Fin Tag.E7.rank | (i : ℕ) < 3} = {e7O8Alpha, e7O8Beta, e7O8Gamma} := by
  ext u
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi3 : (i : ℕ) < 3 := hi
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 by omega) with h | h | h
    · simp [e7EightCols, h]
    · simp [e7EightCols, h]
    · simp [e7EightCols, h]
  · intro hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, by simp, by simp [e7EightCols]⟩
    · exact ⟨⟨1, by decide⟩, by simp, by simp [e7EightCols]⟩
    · exact ⟨⟨2, by decide⟩, by simp, by simp [e7EightCols]⟩

open Polynomial in
theorem e7Eight_block_cyclic {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    IsCyclic (fixedBlockTuples e7O8W Fr {e7O8Alpha, e7O8Beta, e7O8Gamma}) ∧
      Nat.card (fixedBlockTuples e7O8W Fr {e7O8Alpha, e7O8Beta, e7O8Gamma}) = q ^ 4 + 1 := by
  obtain ⟨-, -, -, -, -, hWα, hWβ, hWγ, hβdef, -⟩ :=
    E7_order_eight_lattice_and_exact_three_A1_prime_root_kernel
  have hmem : ∀ u ∈ ({e7O8Alpha, e7O8Beta, e7O8Gamma} : Set (Fin Tag.E7.rank → ℤ)),
      u ∈ Submodule.span ℤ (e7EightCols '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := fun u hu => by
    rw [e7EightCols_image_lt_three]
    exact Submodule.subset_span hu
  have hPmonic : (X ^ 4 + 1 : ℤ[X]).Monic := by
    simpa using Polynomial.monic_X_pow_add_C (R := ℤ) 1 (n := 4) (by norm_num)
  have hPdeg : (X ^ 4 + 1 : ℤ[X]).natDegree = Tag.E7.rank - 3 := by
    have h : (X ^ 4 + 1 : ℤ[X]).natDegree = 4 := by
      rw [show (1 : ℤ[X]) = C 1 from C_1.symm]
      exact Polynomial.natDegree_X_pow_add_C
    rw [h]
    rfl
  have hne : (X ^ 4 + 1 : ℤ[X]).eval (q : ℤ) ≠ 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    positivity
  have h := isCyclic_and_card_fixedBlockTuples (L := L) e7O8W e7EightCols (k := 3) (by decide)
    e7O8V e7EightCols_basis.1 e7EightCols_basis.2
    (fun j hj => by
      have h0 : (j : ℕ) ≠ 0 := by omega
      have h1 : (j : ℕ) ≠ 1 := by omega
      have h2 : (j : ℕ) ≠ 2 := by omega
      simp [e7EightCols, h0, h1, h2])
    (fun j hj => by
      have hj3 : (j : ℕ) < 3 := hj
      rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 by omega) with h | h | h
      · have : e7EightCols j = e7O8Alpha := by simp [e7EightCols, h]
        rw [this, hWα]
        exact hmem _ (by simp)
      · have : e7EightCols j = e7O8Beta := by simp [e7EightCols, h]
        rw [this, hWβ]
        exact hmem _ (by simp)
      · have : e7EightCols j = e7O8Gamma := by simp [e7EightCols, h]
        rw [this, hWγ]
        exact hmem _ (by simp))
    (X ^ 4 + 1) hPmonic hPdeg
    (by
      have h1 : (Polynomial.aeval e7O8W (X ^ 4 + 1 : ℤ[X])) *ᵥ e7O8V =
          e7O8Beta - e7O8Alpha := by
        rw [map_add, map_pow, Polynomial.aeval_X, map_one, Matrix.add_mulVec, Matrix.one_mulVec,
          hβdef]
        abel
      rw [h1]
      exact Submodule.sub_mem _ (hmem _ (by simp)) (hmem _ (by simp)))
    Fr hFr hℓ hℓq (Or.inl (by simp)) hne
  rw [e7EightCols_image_lt_three] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  have e : (q : ℤ) ^ 4 + 1 = ((q ^ 4 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.natAbs_natCast]

theorem e7Eight_rootCharKernel {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : orderOf (q : ZMod p) = 8) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e7O8W Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a =
      {e7O8Alpha, -e7O8Alpha, e7O8Beta, -e7O8Beta, e7O8Gamma, -e7O8Gamma} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmod2, hker, -⟩ :=
    E7_order_eight_lattice_and_exact_three_A1_prime_root_kernel
  obtain ⟨z, hz0, hzM, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples e7O8W Fr hFr hp ha hap ha1
  rw [hzk]
  exact hker p hp hp2 (q : ZMod p) hq z hz0 hzM

end CFSG.RankThree.PartOne.KE
