module

public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.Lattice.SteinbergBIE7OrderFive

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open scoped Matrix Polynomial

@[expose] def e7FiveCols (δ : ℤ) : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ := fun j =>
  if (j : ℕ) = 0 then e7O5Alpha else if (j : ℕ) = 1 then e7O5Theta
  else ((δ • e7O5W) ^ ((j : ℕ) - 2)) *ᵥ e7O5Beta

theorem e7FiveCols_basis (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    LinearIndependent ℤ (e7FiveCols δ) ∧ Submodule.span ℤ (Set.range (e7FiveCols δ)) = ⊤ := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hlin0, hspan0⟩, -⟩ :=
    E7_order_five_lattice_and_exact_A2_prime_root_kernel
  let b : Module.Basis (Fin Tag.E7.rank) ℤ (Fin Tag.E7.rank → ℤ) :=
    Module.Basis.mk hlin0 hspan0.ge
  have hε : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  let ε : ℤˣ := ⟨δ, δ, hε, hε⟩
  let u : Fin Tag.E7.rank → ℤˣ := fun j => if (j : ℕ) < 2 then 1 else ε ^ ((j : ℕ) - 2)
  have hc : ∀ j, (b.unitsSMul u) j = e7FiveCols δ j := by
    intro j
    rw [Module.Basis.unitsSMul_apply]
    have hbj : b j = e7O5Cols j := Module.Basis.mk_apply hlin0 _ j
    rw [hbj]
    by_cases hj0 : (j : ℕ) = 0
    · simp [u, hj0, e7O5Cols, e7FiveCols]
    · by_cases hj1 : (j : ℕ) = 1
      · simp [u, hj1, e7O5Cols, e7FiveCols]
      · have hj2 : ¬ (j : ℕ) < 2 := by omega
        simp only [u, hj2, hj0, hj1, e7O5Cols, e7FiveCols, ite_false, Units.smul_def, smul_pow,
          Matrix.smul_mulVec]
        rw [Units.val_pow_eq_pow_val]
  have hfun : ⇑(b.unitsSMul u) = e7FiveCols δ := funext hc
  rw [← hfun]
  exact ⟨(b.unitsSMul u).linearIndependent, (b.unitsSMul u).span_eq⟩

theorem e7FiveCols_image_lt_two (δ : ℤ) :
    e7FiveCols δ '' {i : Fin Tag.E7.rank | (i : ℕ) < 2} = {e7O5Alpha, e7O5Theta} := by
  ext u
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi2 : (i : ℕ) < 2 := hi
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h
    · simp [e7FiveCols, h]
    · simp [e7FiveCols, h]
  · intro hu
    rcases hu with rfl | rfl
    · exact ⟨⟨0, by decide⟩, by simp, by simp [e7FiveCols]⟩
    · exact ⟨⟨1, by decide⟩, by simp, by simp [e7FiveCols]⟩

open Polynomial in
theorem e7Five_block_cyclic (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples (δ • e7O5W) Fr {e7O5Alpha, e7O5Theta}) ∧
      Nat.card (fixedBlockTuples (δ • e7O5W) Fr {e7O5Alpha, e7O5Theta}) =
        ((q : ℤ) ^ 5 - δ).natAbs := by
  obtain ⟨-, -, -, -, hord, hWα, hWθ, -⟩ :=
    E7_order_five_lattice_and_exact_A2_prime_root_kernel
  have hmem : ∀ x ∈ ({e7O5Alpha, e7O5Theta} : Set (Fin Tag.E7.rank → ℤ)),
      x ∈ Submodule.span ℤ (e7FiveCols δ '' {i : Fin Tag.E7.rank | (i : ℕ) < 2}) := fun x hx => by
    rw [e7FiveCols_image_lt_two]
    exact Submodule.subset_span hx
  have hw5 : e7O5W ^ 5 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hδ5 : δ ^ 5 = δ := by rcases hδ with rfl | rfl <;> norm_num
  have hPmonic : (X ^ 5 - C δ : ℤ[X]).Monic := Polynomial.monic_X_pow_sub_C δ (by norm_num)
  have hPdeg : (X ^ 5 - C δ : ℤ[X]).natDegree = Tag.E7.rank - 2 := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    rfl
  have hq5 : (1 : ℤ) < (q : ℤ) ^ 5 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 5 := by norm_num
      _ ≤ (q : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
  have hne : (X ^ 5 - C δ : ℤ[X]).eval (q : ℤ) ≠ 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rcases hδ with rfl | rfl <;> omega
  have h := isCyclic_and_card_fixedBlockTuples (L := L) (δ • e7O5W) (e7FiveCols δ) (k := 2)
    (by decide) e7O5Beta (e7FiveCols_basis δ hδ).1 (e7FiveCols_basis δ hδ).2
    (fun j hj => by
      have h0 : (j : ℕ) ≠ 0 := by omega
      have h1 : (j : ℕ) ≠ 1 := by omega
      simp [e7FiveCols, h0, h1])
    (fun j hj => by
      have hj2 : (j : ℕ) < 2 := hj
      rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with h | h
      · have : e7FiveCols δ j = e7O5Alpha := by simp [e7FiveCols, h]
        rw [this, Matrix.smul_mulVec, hWα]
        exact Submodule.smul_mem _ δ (hmem _ (by simp))
      · have : e7FiveCols δ j = e7O5Theta := by simp [e7FiveCols, h]
        rw [this, Matrix.smul_mulVec, hWθ]
        exact Submodule.smul_mem _ δ (hmem _ (by simp)))
    (X ^ 5 - C δ) hPmonic hPdeg
    (by
      have h0 : Polynomial.aeval (δ • e7O5W) (X ^ 5 - C δ : ℤ[X]) = 0 := by
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, _root_.smul_pow, hw5, hδ5,
          Algebra.algebraMap_eq_smul_one, sub_self]
      rw [h0, Matrix.zero_mulVec]
      exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (by rcases hδ with rfl | rfl <;> simp [Polynomial.coeff_sub,
      Polynomial.coeff_X_pow]) hne
  rw [e7FiveCols_image_lt_two] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

theorem e7Five_rootCharKernel (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hΦ : ((δ : ZMod p) * q) ^ 4 + ((δ : ZMod p) * q) ^ 3 + ((δ : ZMod p) * q) ^ 2 +
      ((δ : ZMod p) * q) + 1 = 0) {a : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (δ • e7O5W) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = {e7O5Alpha, -e7O5Alpha, e7O5Theta, -e7O5Theta, e7O5Alpha + e7O5Theta,
      -(e7O5Alpha + e7O5Theta)} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hker, -⟩ :=
    E7_order_five_lattice_and_exact_A2_prime_root_kernel
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (δ • e7O5W) Fr hFr hp ha hap ha1
  rw [hzk]
  have hzW : (e7O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((δ : ZMod p) * q) • z := by
    rcases hδ with rfl | rfl
    · simpa using hzM
    · have := transpose_eigen_neg e7O5W (q : ZMod p) z (by simpa using hzM)
      simpa using this
  exact hker p hp hp5 ((δ : ZMod p) * q) hΦ z hz0 hzW

end CFSG.RankThree.PartOne.KE
