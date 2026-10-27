module

public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveMats

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec weylMatrix_pow)
open scoped Matrix Polynomial

@[expose] def e8FiveM (δ : ℤ) : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  δ • weylMatrix e8F5U

theorem e8FiveM_mulVec (δ : ℤ) (x : Fin Tag.E8.rank → ℤ) :
    e8FiveM δ *ᵥ x = δ • (e8F5U • x) := by
  rw [e8FiveM, Matrix.smul_mulVec, weylMatrix_mulVec]

theorem e8FiveM_pow_mulVec (δ : ℤ) (i : ℕ) (x : Fin Tag.E8.rank → ℤ) :
    (e8FiveM δ ^ i) *ᵥ x = (δ ^ i) • ((e8F5U ^ i) • x) := by
  rw [e8FiveM, smul_pow, Matrix.smul_mulVec, ← weylMatrix_pow, weylMatrix_mulVec]

theorem e8F5U_block (o : Fin Tag.E8.rank) (ho : o = 0 ∨ o = 4) :
    e8F5U • e8F5Col o = e8F5Col (o + 1) ∧ e8F5U • e8F5Col (o + 1) = e8F5Col (o + 2) ∧
      e8F5U • e8F5Col (o + 2) = e8F5Col (o + 3) ∧
      e8F5U • e8F5Col (o + 3) = -(e8F5Col o + e8F5Col (o + 1) + e8F5Col (o + 2) +
        e8F5Col (o + 3)) := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7⟩ := e8F5U_cols
  rcases ho with rfl | rfl
  · exact ⟨u0, u1, u2, u3⟩
  · exact ⟨u4, u5, u6, u7⟩

open Polynomial in
@[expose] def e8FiveP (δ : ℤ) : ℤ[X] :=
  X ^ 4 + C δ * X ^ 3 + X ^ 2 + C δ * X + 1

theorem e8FiveP_monic (δ : ℤ) : (e8FiveP δ).Monic := by
  unfold e8FiveP
  monicity!

theorem e8FiveP_natDegree (δ : ℤ) : (e8FiveP δ).natDegree = 4 := by
  unfold e8FiveP
  compute_degree!

theorem e8FiveP_coeff_zero (δ : ℤ) : (e8FiveP δ).coeff 0 = 1 := by
  simp [e8FiveP, Polynomial.coeff_add, Polynomial.coeff_X_pow]

theorem e8FiveP_eval (δ q : ℤ) : (e8FiveP δ).eval q = q ^ 4 + δ * q ^ 3 + q ^ 2 + δ * q + 1 := by
  simp [e8FiveP]

theorem aeval_e8FiveP (δ : ℤ) : Polynomial.aeval (e8FiveM δ) (e8FiveP δ) =
    e8FiveM δ ^ 4 + δ • e8FiveM δ ^ 3 + e8FiveM δ ^ 2 + δ • e8FiveM δ + 1 := by
  simp only [e8FiveP, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    map_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem e8Five_pow_col_one (o : Fin Tag.E8.rank) (ho : o = 0 ∨ o = 4) (δ : ℤ) :
    (e8FiveM δ ^ 1) *ᵥ e8F5Col o = δ • e8F5Col (o + 1) := by
  obtain ⟨b1, -, -, -⟩ := e8F5U_block o ho
  rw [e8FiveM_pow_mulVec, pow_one, pow_one, b1]

theorem e8Five_pow_col_two (o : Fin Tag.E8.rank) (ho : o = 0 ∨ o = 4) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    (e8FiveM δ ^ 2) *ᵥ e8F5Col o = e8F5Col (o + 2) := by
  obtain ⟨b1, b2, -, -⟩ := e8F5U_block o ho
  have h2 : (δ ^ 2 : ℤ) = 1 := by rcases hδ with rfl | rfl <;> norm_num
  rw [e8FiveM_pow_mulVec, h2, one_smul, pow_two, mul_smul, b1, b2]

theorem e8Five_pow_col_three (o : Fin Tag.E8.rank) (ho : o = 0 ∨ o = 4) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    (e8FiveM δ ^ 3) *ᵥ e8F5Col o = δ • e8F5Col (o + 3) := by
  obtain ⟨b1, b2, b3, -⟩ := e8F5U_block o ho
  have h3 : (δ ^ 3 : ℤ) = δ := by rcases hδ with rfl | rfl <;> norm_num
  rw [e8FiveM_pow_mulVec, h3, pow_succ, pow_two, mul_smul, mul_smul, b1, b2, b3]

theorem e8Five_pow_four_col (o : Fin Tag.E8.rank) (ho : o = 0 ∨ o = 4) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    (e8FiveM δ ^ 4) *ᵥ e8F5Col o =
      -(e8F5Col o + e8F5Col (o + 1) + e8F5Col (o + 2) + e8F5Col (o + 3)) := by
  obtain ⟨b1, b2, b3, b4⟩ := e8F5U_block o ho
  have h4 : (δ ^ 4 : ℤ) = 1 := by rcases hδ with rfl | rfl <;> norm_num
  rw [e8FiveM_pow_mulVec, h4, one_smul, pow_succ, pow_succ, pow_two, mul_smul, mul_smul, mul_smul,
    b1, b2, b3, b4]

theorem e8Five_P_col (o : Fin Tag.E8.rank) (ho : o = 0 ∨ o = 4) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ e8F5Col o = 0 := by
  have h1 := e8Five_pow_col_one o ho δ
  rw [pow_one] at h1
  have h2 := e8Five_pow_col_two o ho δ hδ
  have h3 := e8Five_pow_col_three o ho δ hδ
  have h4 := e8Five_pow_four_col o ho δ hδ
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  rw [aeval_e8FiveP, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h4, h2, h3, h1, smul_smul, hδ2,
    one_smul, smul_smul, hδ2, one_smul]
  abel

theorem e8F5Col_basis :
    LinearIndependent ℤ e8F5Col ∧ Submodule.span ℤ (Set.range e8F5Col) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E8.rank)), Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.E8.rank)).toMatrix e8F5Col =
      Matrix.of fun i j => e8F5Col j i := rfl
  have h' : (Matrix.of fun i j => e8F5Col j i) = e8F5B := by
    rw [e8F5B_eq]
    rfl
  rw [h, h', e8F5B_det]
  exact isUnit_one

@[expose] def e8FiveCols (s : Fin Tag.E8.rank) (δ : ℤ) :
    Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := fun j =>
  if (j : ℕ) < 4 then (e8FiveM δ ^ (j : ℕ)) *ᵥ e8F5Col s
  else (e8FiveM δ ^ ((j : ℕ) - 4)) *ᵥ e8F5Col (s + 4)

theorem e8Five_block_mem (s : Fin Tag.E8.rank) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (o : Fin Tag.E8.rank) (hs : s = 0 ∨ s = 4) (ho : o = s ∨ o = s + 4) :
    e8F5Col o ∈ Submodule.span ℤ (Set.range (e8FiveCols s δ)) ∧
      e8F5Col (o + 1) ∈ Submodule.span ℤ (Set.range (e8FiveCols s δ)) ∧
      e8F5Col (o + 2) ∈ Submodule.span ℤ (Set.range (e8FiveCols s δ)) ∧
      e8F5Col (o + 3) ∈ Submodule.span ℤ (Set.range (e8FiveCols s δ)) := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hos : o = 0 ∨ o = 4 := by
    rcases hs with h0 | h0 <;> rcases ho with h1 | h1 <;> subst h0 <;> subst h1 <;> decide
  have h1 := e8Five_pow_col_one o hos δ
  have h2 := e8Five_pow_col_two o hos δ hδ
  have h3 := e8Five_pow_col_three o hos δ hδ
  have hcol1 : e8F5Col (o + 1) = δ • ((e8FiveM δ ^ 1) *ᵥ e8F5Col o) := by
    rw [h1, smul_smul, hδ2, one_smul]
  have hcol3 : e8F5Col (o + 3) = δ • ((e8FiveM δ ^ 3) *ᵥ e8F5Col o) := by
    rw [h3, smul_smul, hδ2, one_smul]
  have hcol2 : e8F5Col (o + 2) = (e8FiveM δ ^ 2) *ᵥ e8F5Col o := h2.symm
  have hcol0 : e8F5Col o = (e8FiveM δ ^ 0) *ᵥ e8F5Col o := by simp
  rcases ho with h | h
  · have c0 : e8FiveCols s δ ⟨0, by decide⟩ = (e8FiveM δ ^ 0) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    have c1 : e8FiveCols s δ ⟨1, by decide⟩ = (e8FiveM δ ^ 1) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    have c2 : e8FiveCols s δ ⟨2, by decide⟩ = (e8FiveM δ ^ 2) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    have c3 : e8FiveCols s δ ⟨3, by decide⟩ = (e8FiveM δ ^ 3) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcol0, ← c0]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hcol1, ← c1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [hcol2, ← c2]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hcol3, ← c3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have c0 : e8FiveCols s δ ⟨4, by decide⟩ = (e8FiveM δ ^ 0) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    have c1 : e8FiveCols s δ ⟨5, by decide⟩ = (e8FiveM δ ^ 1) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    have c2 : e8FiveCols s δ ⟨6, by decide⟩ = (e8FiveM δ ^ 2) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    have c3 : e8FiveCols s δ ⟨7, by decide⟩ = (e8FiveM δ ^ 3) *ᵥ e8F5Col o := by
      rw [h]
      simp [e8FiveCols]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcol0, ← c0]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hcol1, ← c1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [hcol2, ← c2]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hcol3, ← c3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem e8FiveCols_basis (s : Fin Tag.E8.rank) (hs : s = 0 ∨ s = 4) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    LinearIndependent ℤ (e8FiveCols s δ) ∧ Submodule.span ℤ (Set.range (e8FiveCols s δ)) = ⊤ := by
  have hcolmem : ∀ k : Fin Tag.E8.rank,
      e8F5Col k ∈ Submodule.span ℤ (Set.range (e8FiveCols s δ)) := by
    have hA := e8Five_block_mem s δ hδ s hs (Or.inl rfl)
    have hB := e8Five_block_mem s δ hδ (s + 4) hs (Or.inr rfl)
    intro k
    rcases hs with rfl | rfl <;> fin_cases k <;>
      first
        | exact hA.1 | exact hA.2.1 | exact hA.2.2.1 | exact hA.2.2.2
        | exact hB.1 | exact hB.2.1 | exact hB.2.2.1 | exact hB.2.2.2
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range (e8FiveCols s δ)) := by
    rw [← e8F5Col_basis.2, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hcolmem k
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan ?_, top_le_iff.1 hspan⟩
  simp

theorem e8Five_first_block_mem (s : Fin Tag.E8.rank) (hs : s = 0 ∨ s = 4) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    e8F5Col s ∈ Submodule.span ℤ (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ∧
      e8F5Col (s + 1) ∈
        Submodule.span ℤ (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ∧
      e8F5Col (s + 2) ∈
        Submodule.span ℤ (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ∧
      e8F5Col (s + 3) ∈
        Submodule.span ℤ (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have h1 := e8Five_pow_col_one s hs δ
  have h2 := e8Five_pow_col_two s hs δ hδ
  have h3 := e8Five_pow_col_three s hs δ hδ
  have hcol1 : e8F5Col (s + 1) = δ • ((e8FiveM δ ^ 1) *ᵥ e8F5Col s) := by
    rw [h1, smul_smul, hδ2, one_smul]
  have hcol3 : e8F5Col (s + 3) = δ • ((e8FiveM δ ^ 3) *ᵥ e8F5Col s) := by
    rw [h3, smul_smul, hδ2, one_smul]
  have hcol2 : e8F5Col (s + 2) = (e8FiveM δ ^ 2) *ᵥ e8F5Col s := h2.symm
  have hcol0 : e8F5Col s = (e8FiveM δ ^ 0) *ᵥ e8F5Col s := by simp
  have c0 : e8FiveCols s δ ⟨0, by decide⟩ = (e8FiveM δ ^ 0) *ᵥ e8F5Col s := by
    simp [e8FiveCols]
  have c1 : e8FiveCols s δ ⟨1, by decide⟩ = (e8FiveM δ ^ 1) *ᵥ e8F5Col s := by
    simp [e8FiveCols]
  have c2 : e8FiveCols s δ ⟨2, by decide⟩ = (e8FiveM δ ^ 2) *ᵥ e8F5Col s := by
    simp [e8FiveCols]
  have c3 : e8FiveCols s δ ⟨3, by decide⟩ = (e8FiveM δ ^ 3) *ᵥ e8F5Col s := by
    simp [e8FiveCols]
  have hmem : ∀ j : Fin Tag.E8.rank, (j : ℕ) < 4 →
      e8FiveCols s δ j ∈ Submodule.span ℤ
        (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) := fun j hj =>
    Submodule.subset_span ⟨j, hj, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcol0, ← c0]
    exact hmem _ (by decide)
  · rw [hcol1, ← c1]
    exact Submodule.smul_mem _ _ (hmem _ (by decide))
  · rw [hcol2, ← c2]
    exact hmem _ (by decide)
  · rw [hcol3, ← c3]
    exact Submodule.smul_mem _ _ (hmem _ (by decide))

theorem e8Five_stab (s : Fin Tag.E8.rank) (hs : s = 0 ∨ s = 4) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    ∀ j : Fin Tag.E8.rank, (j : ℕ) < 4 →
      e8FiveM δ *ᵥ e8FiveCols s δ j ∈
        Submodule.span ℤ (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) := by
  obtain ⟨m0, m1, m2, m3⟩ := e8Five_first_block_mem s hs δ hδ
  have hmem : ∀ j : Fin Tag.E8.rank, (j : ℕ) < 4 →
      e8FiveCols s δ j ∈ Submodule.span ℤ
        (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) := fun j hj =>
    Submodule.subset_span ⟨j, hj, rfl⟩
  have hstep : ∀ j k : Fin Tag.E8.rank, (j : ℕ) < 3 → (k : ℕ) = (j : ℕ) + 1 →
      e8FiveM δ *ᵥ e8FiveCols s δ j = e8FiveCols s δ k := by
    intro j k hj hk
    have hj4 : (j : ℕ) < 4 := by omega
    have hj1 : (j : ℕ) + 1 < 4 := by omega
    simp [e8FiveCols, hj4, hj1, hk, Matrix.mulVec_mulVec, pow_succ']
  intro j hj
  by_cases hj3 : (j : ℕ) < 3
  · obtain ⟨k, hk⟩ : ∃ k : Fin Tag.E8.rank, (k : ℕ) = (j : ℕ) + 1 :=
      ⟨⟨(j : ℕ) + 1, by have : Tag.E8.rank = 8 := rfl; omega⟩, rfl⟩
    rw [hstep j k hj3 hk]
    exact hmem k (by omega)
  · have hj3' : (j : ℕ) = 3 := by omega
    have hjeq : e8FiveCols s δ j = (e8FiveM δ ^ 3) *ᵥ e8F5Col s := by
      simp [e8FiveCols, hj3']
    rw [hjeq, Matrix.mulVec_mulVec, ← pow_succ', e8Five_pow_four_col s hs δ hδ]
    exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ m0
      m1) m2) m3)

theorem e8FiveP_eval_ne_zero (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {q : ℕ} (hq : 2 ≤ q) :
    (e8FiveP δ).eval (q : ℤ) ≠ 0 := by
  rw [e8FiveP_eval]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have h1 : (0 : ℤ) ≤ (q : ℤ) ^ 3 * ((q : ℤ) - 1) := mul_nonneg (by positivity) (by omega)
  have h2 : (0 : ℤ) ≤ (q : ℤ) * ((q : ℤ) - 1) := mul_nonneg (by positivity) (by omega)
  have h3 : (0 : ℤ) < (q : ℤ) ^ 3 := by positivity
  rcases hδ with rfl | rfl <;> nlinarith

theorem e8Five_block_cyclic (s : Fin Tag.E8.rank) (hs : s = 0 ∨ s = 4) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples (e8FiveM δ) Fr
        (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) ∧
      Nat.card (fixedBlockTuples (e8FiveM δ) Fr
        (e8FiveCols s δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) =
          ((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs := by
  have hs4 : s + 4 = 0 ∨ s + 4 = 4 := by rcases hs with rfl | rfl <;> decide
  have h := isCyclic_and_card_fixedBlockTuples (L := L) (e8FiveM δ) (e8FiveCols s δ) (k := 4)
    (by decide) (e8F5Col (s + 4)) (e8FiveCols_basis s hs δ hδ).1 (e8FiveCols_basis s hs δ hδ).2
    (fun j hj => by
      have hj4 : ¬ (j : ℕ) < 4 := by omega
      simp [e8FiveCols, hj4])
    (e8Five_stab s hs δ hδ) (e8FiveP δ) (e8FiveP_monic δ)
    (by rw [e8FiveP_natDegree]; rfl)
    (by rw [e8Five_P_col (s + 4) hs4 δ hδ]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (Or.inl (e8FiveP_coeff_zero δ)) (e8FiveP_eval_ne_zero δ hδ hq)
  refine ⟨h.1, ?_⟩
  rw [h.2, e8FiveP_eval]

theorem e8Five_inf_eq_bot (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] (Fr : L →+* L) :
    fixedBlockTuples (e8FiveM δ) Fr (e8FiveCols 4 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ⊓
      fixedBlockTuples (e8FiveM δ) Fr (e8FiveCols 0 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) =
        ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  obtain ⟨a4_0, a4_1, a4_2, a4_3⟩ := e8Five_first_block_mem 4 (Or.inr rfl) δ hδ
  obtain ⟨a0_0, a0_1, a0_2, a0_3⟩ := e8Five_first_block_mem 0 (Or.inl rfl) δ hδ
  have hS : ∀ u ∈ Set.range e8F5Col, rootChar a u = 1 := by
    rintro _ ⟨k, rfl⟩
    have h4 := (mem_fixedBlockTuples.1 ha1).2
    have h0 := (mem_fixedBlockTuples.1 ha2).2
    fin_cases k <;>
      first
        | exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_0
        | exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_1
        | exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_2
        | exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_3
        | exact CTTorus.rootChar_eq_one_of_mem_span h4 a4_0
        | exact CTTorus.rootChar_eq_one_of_mem_span h4 a4_1
        | exact CTTorus.rootChar_eq_one_of_mem_span h4 a4_2
        | exact CTTorus.rootChar_eq_one_of_mem_span h4 a4_3
  have h1 : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u => by
    refine CTTorus.rootChar_eq_one_of_mem_span hS ?_
    rw [e8F5Col_basis.2]
    exact Submodule.mem_top
  exact h1 ▸ Subgroup.one_mem _

theorem card_sup_of_inf_eq_bot {G : Type*} [CommGroup G] {A B : Subgroup G} [Finite A] [Finite B]
    (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let φ : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype fun _ _ => Commute.all _ _
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := by simpa [φ] using hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : G) ∈ A ⊓ B :=
      ⟨x.2, by rw [hx]; exact B.inv_mem y.2⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hy : (y : G) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofInjective φ hinj)).symm

theorem e8Five_P_zero (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (x : Fin Tag.E8.rank → ℤ) :
    (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ x = 0 := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hcomm : ∀ i : ℕ, Commute (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) (e8FiveM δ ^ i) :=
    fun i => ((Algebra.commute_of_mem_adjoin_self
      (Polynomial.aeval_mem_adjoin_singleton ℤ (e8FiveM δ))).pow_left i).symm
  have hpow : ∀ (o : Fin Tag.E8.rank), (o = 0 ∨ o = 4) → ∀ i : ℕ,
      (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ ((e8FiveM δ ^ i) *ᵥ e8F5Col o) = 0 := by
    intro o ho i
    rw [Matrix.mulVec_mulVec, (hcomm i).eq, ← Matrix.mulVec_mulVec, e8Five_P_col o ho δ hδ,
      Matrix.mulVec_zero]
  have hcol : ∀ k : Fin Tag.E8.rank,
      (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ e8F5Col k = 0 := by
    intro k
    have hP0 := e8Five_P_col 0 (Or.inl rfl) δ hδ
    have hP4 := e8Five_P_col 4 (Or.inr rfl) δ hδ
    have c1 := e8Five_pow_col_one 0 (Or.inl rfl) δ
    have c2 := e8Five_pow_col_two 0 (Or.inl rfl) δ hδ
    have c3 := e8Five_pow_col_three 0 (Or.inl rfl) δ hδ
    have d1 := e8Five_pow_col_one 4 (Or.inr rfl) δ
    have d2 := e8Five_pow_col_two 4 (Or.inr rfl) δ hδ
    have d3 := e8Five_pow_col_three 4 (Or.inr rfl) δ hδ
    have e1 : ∀ o : Fin Tag.E8.rank, (o = 0 ∨ o = 4) → ∀ y : Fin Tag.E8.rank → ℤ,
        y = δ • ((e8FiveM δ ^ 1) *ᵥ e8F5Col o) →
          (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ y = 0 := fun o ho y hy => by
      rw [hy, Matrix.mulVec_smul, hpow o ho 1, smul_zero]
    have e2 : ∀ o : Fin Tag.E8.rank, (o = 0 ∨ o = 4) → ∀ y : Fin Tag.E8.rank → ℤ,
        y = (e8FiveM δ ^ 2) *ᵥ e8F5Col o →
          (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ y = 0 := fun o ho y hy => by
      rw [hy, hpow o ho 2]
    have e3 : ∀ o : Fin Tag.E8.rank, (o = 0 ∨ o = 4) → ∀ y : Fin Tag.E8.rank → ℤ,
        y = δ • ((e8FiveM δ ^ 3) *ᵥ e8F5Col o) →
          (Polynomial.aeval (e8FiveM δ) (e8FiveP δ)) *ᵥ y = 0 := fun o ho y hy => by
      rw [hy, Matrix.mulVec_smul, hpow o ho 3, smul_zero]
    have g1 : ∀ o : Fin Tag.E8.rank, (o = 0 ∨ o = 4) →
        e8F5Col (o + 1) = δ • ((e8FiveM δ ^ 1) *ᵥ e8F5Col o) := fun o ho => by
      rw [e8Five_pow_col_one o ho δ, smul_smul, hδ2, one_smul]
    have g2 : ∀ o : Fin Tag.E8.rank, (o = 0 ∨ o = 4) →
        e8F5Col (o + 2) = (e8FiveM δ ^ 2) *ᵥ e8F5Col o := fun o ho =>
      (e8Five_pow_col_two o ho δ hδ).symm
    have g3 : ∀ o : Fin Tag.E8.rank, (o = 0 ∨ o = 4) →
        e8F5Col (o + 3) = δ • ((e8FiveM δ ^ 3) *ᵥ e8F5Col o) := fun o ho => by
      rw [e8Five_pow_col_three o ho δ hδ, smul_smul, hδ2, one_smul]
    fin_cases k <;>
      first
        | exact hP0
        | exact hP4
        | exact e1 0 (Or.inl rfl) _ (g1 0 (Or.inl rfl))
        | exact e2 0 (Or.inl rfl) _ (g2 0 (Or.inl rfl))
        | exact e3 0 (Or.inl rfl) _ (g3 0 (Or.inl rfl))
        | exact e1 4 (Or.inr rfl) _ (g1 4 (Or.inr rfl))
        | exact e2 4 (Or.inr rfl) _ (g2 4 (Or.inr rfl))
        | exact e3 4 (Or.inr rfl) _ (g3 4 (Or.inr rfl))
  have hx : x ∈ Submodule.span ℤ (Set.range e8F5Col) := by
    rw [e8F5Col_basis.2]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact hcol k
  | zero => exact Matrix.mulVec_zero _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz, add_zero]
  | smul n y _ hy => rw [Matrix.mulVec_smul, hy, smul_zero]

theorem e8Five_zpow_eq_one (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] (Fr : L →+* L)
    {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e8FiveM δ) Fr) (i : Fin Tag.E8.rank) :
    a i ^ ((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1) = 1 := by
  have h := rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr ha (e8FiveP δ) (Pi.single i 1)
  rw [e8Five_P_zero δ hδ, rootChar_zero, CTTorus.rootChar_single, e8FiveP_eval] at h
  exact h.symm

theorem e8Five_orderOf_dvd (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] (Fr : L →+* L)
    {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e8FiveM δ) Fr) :
    orderOf a ∣ ((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs := by
  apply orderOf_dvd_of_pow_eq_one
  funext i
  have h := e8Five_zpow_eq_one δ hδ Fr hFr ha i
  rw [Pi.pow_apply, Pi.one_apply]
  rcases Int.natAbs_eq ((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1) with hF | hF
  · rw [hF] at h
    simpa using h
  · rw [hF, zpow_neg, inv_eq_one] at h
    simpa using h

theorem e8Five_eigencolumn (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] (Fr : L →+* L)
    {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e8FiveM δ) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ z : Fin Tag.E8.rank → ZMod p, z ≠ 0 ∧
      (dualMatrix (ZMod p) e8F5U).mulVec z = ((δ : ZMod p) * (q : ZMod p)) • z ∧
        rootCharKernel a = e8RootKernel z := by
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (e8FiveM δ) Fr hFr hp ha hap ha1
  refine ⟨z, hz0, ?_, hzk⟩
  have hM : ((e8FiveM δ).map (Int.cast : ℤ → ZMod p))ᵀ =
      (δ : ZMod p) • dualMatrix (ZMod p) e8F5U := by
    ext i j
    simp only [e8FiveM, dualMatrix, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, Int.cast_mul]
  rw [hM, Matrix.smul_mulVec] at hzM
  have hδ2 : (δ : ZMod p) * (δ : ZMod p) = 1 := by
    rcases hδ with h | h <;> rw [h] <;> simp
  calc (dualMatrix (ZMod p) e8F5U).mulVec z
      = ((δ : ZMod p) * (δ : ZMod p)) • (dualMatrix (ZMod p) e8F5U).mulVec z := by
        rw [hδ2, one_smul]
    _ = (δ : ZMod p) • ((δ : ZMod p) • (dualMatrix (ZMod p) e8F5U).mulVec z) := by
        rw [mul_smul]
    _ = (δ : ZMod p) • ((q : ZMod p) • z) := by rw [hzM]
    _ = ((δ : ZMod p) * (q : ZMod p)) • z := by rw [mul_smul]

theorem e8Five_card_sup (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    Nat.card ↥(fixedBlockTuples (e8FiveM δ) Fr
        (e8FiveCols 4 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ⊔
      fixedBlockTuples (e8FiveM δ) Fr
        (e8FiveCols 0 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) =
      ((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs ^ 2 := by
  obtain ⟨-, h4⟩ := e8Five_block_cyclic 4 (Or.inr rfl) δ hδ Fr hFr hℓ hℓq hq
  obtain ⟨-, h0⟩ := e8Five_block_cyclic 0 (Or.inl rfl) δ hδ Fr hFr hℓ hℓq hq
  have hne : ((q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs ≠ 0 := by
    have := e8FiveP_eval_ne_zero δ hδ hq
    rw [e8FiveP_eval] at this
    exact Int.natAbs_ne_zero.2 this
  have : Finite ↥(fixedBlockTuples (e8FiveM δ) Fr
      (e8FiveCols 4 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) :=
    Nat.finite_of_card_ne_zero (by rw [h4]; exact hne)
  have : Finite ↥(fixedBlockTuples (e8FiveM δ) Fr
      (e8FiveCols 0 δ '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) :=
    Nat.finite_of_card_ne_zero (by rw [h0]; exact hne)
  rw [card_sup_of_inf_eq_bot (e8Five_inf_eq_bot δ hδ Fr), h4, h0]
  exact (sq _).symm

end CFSG.RankThree.PartOne.KE
