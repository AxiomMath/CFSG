module

public import CFSG.RankThree.Classical.OrthogonalOrderThree

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
open scoped Matrix commutatorElement

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_orderOf_eq_three_statedProj {H : Subgroup (GL ι K)} {g : GL ι K} (hgH : g ∈ H)
    (hg3 : g ^ 3 = 1) (hgs : g ∉ StatedScalars ι K) : ∃ y : StatedProj H, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨(QuotientGroup.mk ⟨g, hgH⟩ : StatedProj H), orderOf_eq_prime ?_ ?_⟩
  · rw [← QuotientGroup.mk_pow]
    have h : (⟨g, hgH⟩ : H) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg3)
    rw [h, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hgs

theorem not_mem_statedScalars_of_ne_zero {g : GL ι K} {i j : ι} (hij : i ≠ j)
    (h : (g : Matrix ι ι K) i j ≠ 0) : g ∉ StatedScalars ι K := by
  rintro ⟨c, rfl⟩
  apply h
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

end Generic

section OrderThree

variable {K : Type} [Field K]

@[expose] def mThree (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

theorem mThree_pow_three : mThree K * (mThree K * mThree K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mThree, Matrix.mul_apply, Fin.sum_univ_two]

theorem mThree_mul_pow_two : (mThree K * mThree K) * mThree K = 1 := by
  rw [Matrix.mul_assoc, mThree_pow_three]

@[expose] def glThree (K : Type) [Field K] : GL (Fin 2) K :=
  ⟨mThree K, mThree K * mThree K, mThree_pow_three, mThree_mul_pow_two⟩

theorem glThree_pow_three : glThree K ^ 3 = 1 := by
  ext1
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change mThree K ^ 3 = 1
  rw [pow_three]
  exact mThree_pow_three

theorem det_glThree : ((glThree K : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
  change (mThree K).det = 1
  simp [mThree, Matrix.det_fin_two]

theorem glThree_not_mem_statedScalars : glThree K ∉ StatedScalars (Fin 2) K :=
  not_mem_statedScalars_of_ne_zero (i := 0) (j := 1) (by decide) (by simp [glThree, mThree])

theorem sign_commutatorElement {α : Type} [Fintype α] [DecidableEq α] (s t : Equiv.Perm α) :
    Equiv.Perm.sign ⁅s, t⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]

theorem exists_gl_pow_three_eq_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ g : GL (Fin n) K, g ^ 3 = 1 ∧ g ∉ StatedScalars (Fin n) K ∧
      (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · exact ⟨glThree K, glThree_pow_three, glThree_not_mem_statedScalars, det_glThree⟩
  · obtain ⟨h3, hne⟩ := orderOf_commutator_swap_swap hn3
    set ρ := ⁅Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩,
      Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩⁆
    refine ⟨permGL ρ, by rw [← map_pow, h3, map_one], permGL_not_mem_statedScalars hne, ?_⟩
    rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation, map_inv,
      sign_commutatorElement, inv_one, Units.val_one, Int.cast_one]

end OrderThree

section Models

variable {K : Type} [Field K]

theorem exists_orderOf_eq_three_statedProj_statedSL {n : ℕ} (hn : 2 ≤ n) :
    ∃ y : StatedProj (StatedSL n K), orderOf y = 3 := by
  obtain ⟨g, hg3, hgs, hdet⟩ := exists_gl_pow_three_eq_one (K := K) hn
  exact exists_orderOf_eq_three_statedProj (Subgroup.subset_closure hdet) hg3 hgs

theorem permMatrix_map_pow {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) {q : ℕ}
    (hq : q ≠ 0) : (σ.permMatrix K).map (· ^ q) = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp [hq]

theorem exists_orderOf_eq_three_statedProj_statedSU {n q : ℕ} (hn : 3 ≤ n) (hq : q ≠ 0) :
    ∃ y : StatedProj (StatedSU n q K), orderOf y = 3 := by
  obtain ⟨h3, hne⟩ := orderOf_commutator_swap_swap hn
  set ρ := ⁅Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩,
    Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩⁆
  refine exists_orderOf_eq_three_statedProj (g := permGL ρ) (Subgroup.subset_closure ⟨?_, ?_⟩)
    (by rw [← map_pow, h3, map_one]) (permGL_not_mem_statedScalars hne)
  · rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation, map_inv,
      sign_commutatorElement, inv_one, Units.val_one, Int.cast_one]
  · rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, permMatrix_map_pow _ hq,
      Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrixHom_apply,
      show Equiv.Perm.permMatrix K ρ = Matrix.permMatrixHom ρ⁻¹ by
        rw [Matrix.permMatrixHom_apply, inv_inv],
      ← map_mul, inv_mul_cancel, map_one]

@[expose] def spEmbed (n : ℕ) (K : Type) [Field K] : GL (Fin n) K →* GL (Fin n ⊕ Fin n) K where
  toFun B := ⟨Matrix.fromBlocks (B : Matrix (Fin n) (Fin n) K) 0 0
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ,
    Matrix.fromBlocks ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0
      (B : Matrix (Fin n) (Fin n) K)ᵀ,
    by
      rw [Matrix.fromBlocks_multiply]
      simp [← Matrix.transpose_mul, Matrix.fromBlocks_one],
    by
      rw [Matrix.fromBlocks_multiply]
      simp [← Matrix.transpose_mul, Matrix.fromBlocks_one]⟩
  map_one' := by
    ext1
    simp [Matrix.fromBlocks_one]
  map_mul' B C := by
    ext1
    simp [Matrix.fromBlocks_multiply, Matrix.transpose_mul]

theorem spEmbed_mem_statedSp {n : ℕ} (B : GL (Fin n) K) : spEmbed n K B ∈ StatedSp n K := by
  refine Subgroup.subset_closure ?_
  change (Matrix.fromBlocks (B : Matrix (Fin n) (Fin n) K) 0 0
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
    Matrix.fromBlocks (B : Matrix (Fin n) (Fin n) K) 0 0
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = Matrix.fromBlocks 0 1 (-1) 0
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [← Matrix.transpose_mul]

theorem spEmbed_not_mem_statedScalars {n : ℕ} {B : GL (Fin n) K}
    (hB : B ∉ StatedScalars (Fin n) K) : spEmbed n K B ∉ StatedScalars (Fin n ⊕ Fin n) K := by
  rintro ⟨c, hc⟩
  apply hB
  refine ⟨c, Units.ext ?_⟩
  ext i j
  have h := congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl i) (Sum.inl j)) hc
  simpa [spEmbed, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply] using h

theorem exists_orderOf_eq_three_statedProj_statedSp {n : ℕ} (hn : 2 ≤ n) :
    ∃ y : StatedProj (StatedSp n K), orderOf y = 3 := by
  obtain ⟨g, hg3, hgs, -⟩ := exists_gl_pow_three_eq_one (K := K) hn
  exact exists_orderOf_eq_three_statedProj (spEmbed_mem_statedSp g)
    (by rw [← map_pow, hg3, map_one]) (spEmbed_not_mem_statedScalars hgs)

end Models

theorem classicalModel_exists_orderOf_eq_three {T : Type} [Group T] {t : StatedLieTag}
    {n p f : ℕ} (hT : StatedClassicalModel T t n p f) :
    (∃ x : T, orderOf x = 3) ∧ 3 ∣ Nat.card T := by
  suffices h : ∃ x : T, orderOf x = 3 by
    obtain ⟨x, hx⟩ := h
    exact ⟨⟨x, hx⟩, hx ▸ orderOf_dvd_natCard x⟩
  obtain ⟨hadm, hm⟩ := hT
  cases t with
  | PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hm
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedSL (K := K) hn
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  | PSU =>
    obtain ⟨hp, -, hn, -⟩ := hadm
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hm
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedSU (K := K) hn
      (pow_ne_zero _ hp.ne_zero)
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  | PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hm
    obtain ⟨y, hy⟩ := exists_orderOf_eq_three_statedProj_statedSp (K := K) hn
    exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  | POmegaOdd => exact (orthogonal_model_exists_orderOf_eq_three (Or.inl rfl) ⟨hadm, hm⟩).1
  | POmegaPlus =>
    exact (orthogonal_model_exists_orderOf_eq_three (Or.inr (Or.inl rfl)) ⟨hadm, hm⟩).1
  | POmegaMinus =>
    exact (orthogonal_model_exists_orderOf_eq_three (Or.inr (Or.inr rfl)) ⟨hadm, hm⟩).1
  | _ => exact hm.elim

end CFSG.RankThree.PartTwo.KFacts.KS14
