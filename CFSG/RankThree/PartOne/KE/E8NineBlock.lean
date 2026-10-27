module

public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderNine

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open scoped Matrix Polynomial

@[expose] def e8NineCols (δ : ℤ) : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := fun j =>
  if (j : ℕ) = 0 then e8O9Alpha else if (j : ℕ) = 1 then e8O9Theta
  else ((δ • e8O9W) ^ ((j : ℕ) - 2)) *ᵥ e8O9Beta

theorem e8NineCols_basis (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    LinearIndependent ℤ (e8NineCols δ) ∧ Submodule.span ℤ (Set.range (e8NineCols δ)) = ⊤ := by
  obtain ⟨-, -, -, -, -, -, ⟨hlin0, hspan0⟩, -⟩ :=
    E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel
  let b : Module.Basis (Fin Tag.E8.rank) ℤ (Fin Tag.E8.rank → ℤ) :=
    Module.Basis.mk hlin0 hspan0.ge
  have hε : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  let ε : ℤˣ := ⟨δ, δ, hε, hε⟩
  let u : Fin Tag.E8.rank → ℤˣ := fun j => if (j : ℕ) < 2 then 1 else ε ^ ((j : ℕ) - 2)
  have hc : ∀ j, (b.unitsSMul u) j = e8NineCols δ j := by
    intro j
    rw [Module.Basis.unitsSMul_apply]
    have hbj : b j = e8O9Cols j := Module.Basis.mk_apply hlin0 _ j
    rw [hbj]
    by_cases hj0 : (j : ℕ) = 0
    · simp [u, hj0, e8O9Cols, e8NineCols]
    · by_cases hj1 : (j : ℕ) = 1
      · simp [u, hj1, e8O9Cols, e8NineCols]
      · have hj2 : ¬ (j : ℕ) < 2 := by omega
        simp only [u, hj2, hj0, hj1, e8O9Cols, e8NineCols, ite_false, Units.smul_def, smul_pow,
          Matrix.smul_mulVec]
        rw [Units.val_pow_eq_pow_val]
  have hfun : ⇑(b.unitsSMul u) = e8NineCols δ := funext hc
  rw [← hfun]
  exact ⟨(b.unitsSMul u).linearIndependent, (b.unitsSMul u).span_eq⟩

theorem e8NineCols_image_lt_two (δ : ℤ) :
    e8NineCols δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 2} = {e8O9Alpha, e8O9Theta} := by
  ext u
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi2 : (i : ℕ) < 2 := hi
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h
    · simp [e8NineCols, h]
    · simp [e8NineCols, h]
  · intro hu
    rcases hu with rfl | rfl
    · exact ⟨⟨0, by decide⟩, by simp, by simp [e8NineCols]⟩
    · exact ⟨⟨1, by decide⟩, by simp, by simp [e8NineCols]⟩

theorem aeval_nine_poly (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    Polynomial.aeval (δ • e8O9W) (Polynomial.X ^ 6 + Polynomial.C δ * Polynomial.X ^ 3 + 1 : ℤ[X]) =
      e8O9W ^ 6 + e8O9W ^ 3 + 1 := by
  rcases hδ with rfl | rfl
  · simp [Polynomial.aeval_def]
  · simp [Polynomial.aeval_def]
    rw [Even.neg_pow (by decide), Odd.neg_pow (by decide), neg_neg]

theorem e8Nine_block_cyclic (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples (δ • e8O9W) Fr {e8O9Alpha, e8O9Theta}) ∧
      Nat.card (fixedBlockTuples (δ • e8O9W) Fr {e8O9Alpha, e8O9Theta}) =
        ((q : ℤ) ^ 6 + δ * (q : ℤ) ^ 3 + 1).natAbs := by
  obtain ⟨-, -, -, -, hWα, hWθ, -, -, hrel0, -⟩ :=
    E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel
  have hmem : ∀ x ∈ ({e8O9Alpha, e8O9Theta} : Set (Fin Tag.E8.rank → ℤ)),
      x ∈ Submodule.span ℤ (e8NineCols δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 2}) := fun x hx => by
    rw [e8NineCols_image_lt_two]
    exact Submodule.subset_span hx
  have hq3 : (8 : ℤ) ≤ (q : ℤ) ^ 3 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ (q : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have hne : (Polynomial.X ^ 6 + Polynomial.C δ * Polynomial.X ^ 3 + 1 : ℤ[X]).eval (q : ℤ) ≠
      0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one]
    have h6 : (q : ℤ) ^ 6 = (q : ℤ) ^ 3 * (q : ℤ) ^ 3 := by ring
    rcases hδ with rfl | rfl <;> nlinarith
  have h := isCyclic_and_card_fixedBlockTuples (L := L) (δ • e8O9W) (e8NineCols δ) (k := 2)
    (by decide) e8O9Beta (e8NineCols_basis δ hδ).1 (e8NineCols_basis δ hδ).2
    (fun j hj => by
      have h0 : (j : ℕ) ≠ 0 := by omega
      have h1 : (j : ℕ) ≠ 1 := by omega
      simp [e8NineCols, h0, h1])
    (fun j hj => by
      have hj2 : (j : ℕ) < 2 := hj
      rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with h | h
      · have : e8NineCols δ j = e8O9Alpha := by simp [e8NineCols, h]
        rw [this, Matrix.smul_mulVec, hWα]
        exact Submodule.smul_mem _ δ (hmem _ (by simp))
      · have : e8NineCols δ j = e8O9Theta := by simp [e8NineCols, h]
        rw [this, Matrix.smul_mulVec, hWθ]
        exact Submodule.smul_mem _ δ (hmem _ (by simp)))
    (Polynomial.X ^ 6 + Polynomial.C δ * Polynomial.X ^ 3 + 1) (by monicity!)
    (by compute_degree!)
    (by
      rw [aeval_nine_poly δ hδ, hrel0]
      exact Submodule.sub_mem _ (hmem _ (by simp)) (hmem _ (by simp)))
    Fr hFr hℓ hℓq (Or.inl (by simp [Polynomial.coeff_add, Polynomial.coeff_X_pow])) hne
  rw [e8NineCols_image_lt_two] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]

theorem e8Nine_rootCharKernel (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hΦ : ((δ : ZMod p) * q) ^ 6 + ((δ : ZMod p) * q) ^ 3 + 1 = 0) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (δ • e8O9W) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = {e8O9Alpha, -e8O9Alpha, e8O9Theta, -e8O9Theta, e8O9Alpha + e8O9Theta,
      -(e8O9Alpha + e8O9Theta)} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hker, -⟩ :=
    E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (δ • e8O9W) Fr hFr hp ha hap ha1
  rw [hzk]
  have hzW : (e8O9W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((δ : ZMod p) * q) • z := by
    rcases hδ with rfl | rfl
    · simpa using hzM
    · have := transpose_eigen_neg e8O9W (q : ZMod p) z (by simpa using hzM)
      simpa using this
  exact hker p hp hp3 ((δ : ZMod p) * q) hΦ z hz0 hzW

end CFSG.RankThree.PartOne.KE
