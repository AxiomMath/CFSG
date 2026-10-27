module

public import CFSG.RankThree.PartOne.KE.E6FourBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec weylMatrix_pow)
open scoped Matrix Polynomial

@[expose] def e6SM (δ : ℤ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  δ • weylMatrix e6F4U

theorem e6SM_pow_mulVec (δ : ℤ) (i : ℕ) (x : Fin Tag.E6.rank → ℤ) :
    (e6SM δ ^ i) *ᵥ x = (δ ^ i) • ((e6FourM ^ i) *ᵥ x) := by
  rw [e6SM, smul_pow, Matrix.smul_mulVec]
  rfl

open Polynomial in
@[expose] def e6SP (δ : ℤ) : ℤ[X] :=
  X ^ 3 - C δ * X ^ 2 + X - C δ

theorem e6SP_monic (δ : ℤ) : (e6SP δ).Monic := by
  unfold e6SP
  monicity!

theorem e6SP_natDegree (δ : ℤ) : (e6SP δ).natDegree = 3 := by
  unfold e6SP
  compute_degree!

theorem e6SP_coeff_zero (δ : ℤ) : (e6SP δ).coeff 0 = -δ := by
  simp [e6SP, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow]

theorem e6SP_eval (δ q : ℤ) : (e6SP δ).eval q = q ^ 3 - δ * q ^ 2 + q - δ := by
  simp [e6SP]

theorem e6SP_eval_eq (δ q : ℤ) : (e6SP δ).eval q = (q - δ) * (q ^ 2 + 1) := by
  rw [e6SP_eval]
  ring

theorem e6SP_eval_ne_zero {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {q : ℕ} (hq : 2 ≤ q) :
    (e6SP δ).eval (q : ℤ) ≠ 0 := by
  rw [e6SP_eval_eq]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  refine mul_ne_zero ?_ (by positivity)
  rcases hδ with rfl | rfl <;> omega

theorem aeval_e6SP (δ : ℤ) :
    Polynomial.aeval (e6SM δ) (e6SP δ) = e6SM δ ^ 3 - δ • e6SM δ ^ 2 + e6SM δ - δ • 1 := by
  simp only [e6SP, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem e6S_pow_col_one (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) (δ : ℤ) :
    (e6SM δ ^ 1) *ᵥ e6F4Col o = δ • e6F4Col (o + 1) := by
  rw [e6SM_pow_mulVec, e6Four_pow_col_one o ho, pow_one]

theorem e6S_pow_col_two (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) : (e6SM δ ^ 2) *ᵥ e6F4Col o = e6F4Col (o + 2) := by
  have h2 : (δ ^ 2 : ℤ) = 1 := by rcases hδ with rfl | rfl <;> norm_num
  rw [e6SM_pow_mulVec, e6Four_pow_col_two o ho, h2, one_smul]

theorem e6S_pow_col_three (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    (e6SM δ ^ 3) *ᵥ e6F4Col o = δ • (e6F4Col (o + 2) - e6F4Col (o + 1) + e6F4Col o) := by
  have h3 : (δ ^ 3 : ℤ) = δ := by rcases hδ with rfl | rfl <;> norm_num
  rw [e6SM_pow_mulVec, e6Four_pow_col_three o ho, h3]

theorem e6S_P_col (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) : (Polynomial.aeval (e6SM δ) (e6SP δ)) *ᵥ e6F4Col o = 0 := by
  have h1 := e6S_pow_col_one o ho δ
  rw [pow_one] at h1
  have h2 := e6S_pow_col_two o ho δ hδ
  have h3 := e6S_pow_col_three o ho δ hδ
  rw [aeval_e6SP, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, h3, h2, h1]
  simp only [smul_sub, smul_add]
  abel

@[expose] def e6SCols (s : Fin Tag.E6.rank) (δ : ℤ) :
    Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := fun j =>
  if (j : ℕ) < 3 then (e6SM δ ^ (j : ℕ)) *ᵥ e6F4Col s
  else (e6SM δ ^ ((j : ℕ) - 3)) *ᵥ e6F4Col (s + 3)

theorem e6SCols_eq (s : Fin Tag.E6.rank) (δ : ℤ) (j : Fin Tag.E6.rank) :
    e6SCols s δ j =
      (δ ^ (if (j : ℕ) < 3 then (j : ℕ) else (j : ℕ) - 3)) • e6FourCols s j := by
  unfold e6SCols e6FourCols
  split_ifs
  · rw [e6SM_pow_mulVec]
  · rw [e6SM_pow_mulVec]

theorem e6SCols_basis (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    LinearIndependent ℤ (e6SCols s δ) ∧ Submodule.span ℤ (Set.range (e6SCols s δ)) = ⊤ := by
  obtain ⟨hlin0, hspan0⟩ := e6FourCols_basis s hs
  let b : Module.Basis (Fin Tag.E6.rank) ℤ (Fin Tag.E6.rank → ℤ) :=
    Module.Basis.mk hlin0 hspan0.ge
  have hε : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  let ε : ℤˣ := ⟨δ, δ, hε, hε⟩
  let u : Fin Tag.E6.rank → ℤˣ := fun j =>
    ε ^ (if (j : ℕ) < 3 then (j : ℕ) else (j : ℕ) - 3)
  have hc : ∀ j, (b.unitsSMul u) j = e6SCols s δ j := by
    intro j
    rw [Module.Basis.unitsSMul_apply, Module.Basis.mk_apply hlin0 _ j, e6SCols_eq,
      Units.smul_def]
    simp only [u, Units.val_pow_eq_pow_val]
    rfl
  have hfun : ⇑(b.unitsSMul u) = e6SCols s δ := funext hc
  rw [← hfun]
  exact ⟨(b.unitsSMul u).linearIndependent, (b.unitsSMul u).span_eq⟩

theorem e6S_first_block_mem (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    e6F4Col s ∈ Submodule.span ℤ (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ∧
      e6F4Col (s + 1) ∈
        Submodule.span ℤ (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ∧
      e6F4Col (s + 2) ∈
        Submodule.span ℤ (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have h1 := e6S_pow_col_one s hs δ
  have h2 := e6S_pow_col_two s hs δ hδ
  have hcol1 : e6F4Col (s + 1) = δ • ((e6SM δ ^ 1) *ᵥ e6F4Col s) := by
    rw [h1, smul_smul, hδ2, one_smul]
  have hcol2 : e6F4Col (s + 2) = (e6SM δ ^ 2) *ᵥ e6F4Col s := h2.symm
  have hcol0 : e6F4Col s = (e6SM δ ^ 0) *ᵥ e6F4Col s := by simp
  have c0 : e6SCols s δ ⟨0, by decide⟩ = (e6SM δ ^ 0) *ᵥ e6F4Col s := by simp [e6SCols]
  have c1 : e6SCols s δ ⟨1, by decide⟩ = (e6SM δ ^ 1) *ᵥ e6F4Col s := by simp [e6SCols]
  have c2 : e6SCols s δ ⟨2, by decide⟩ = (e6SM δ ^ 2) *ᵥ e6F4Col s := by simp [e6SCols]
  have hmem : ∀ j : Fin Tag.E6.rank, (j : ℕ) < 3 →
      e6SCols s δ j ∈ Submodule.span ℤ
        (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := fun j hj =>
    Submodule.subset_span ⟨j, hj, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hcol0, ← c0]
    exact hmem _ (by decide)
  · rw [hcol1, ← c1]
    exact Submodule.smul_mem _ _ (hmem _ (by decide))
  · rw [hcol2, ← c2]
    exact hmem _ (by decide)

theorem e6S_stab (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    ∀ j : Fin Tag.E6.rank, (j : ℕ) < 3 →
      e6SM δ *ᵥ e6SCols s δ j ∈
        Submodule.span ℤ (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := by
  obtain ⟨m0, m1, m2⟩ := e6S_first_block_mem s hs δ hδ
  have hmem : ∀ j : Fin Tag.E6.rank, (j : ℕ) < 3 →
      e6SCols s δ j ∈ Submodule.span ℤ
        (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := fun j hj =>
    Submodule.subset_span ⟨j, hj, rfl⟩
  have hstep : ∀ j k : Fin Tag.E6.rank, (j : ℕ) < 2 → (k : ℕ) = (j : ℕ) + 1 →
      e6SM δ *ᵥ e6SCols s δ j = e6SCols s δ k := by
    intro j k hj hk
    have hj3 : (j : ℕ) < 3 := by omega
    have hk3 : (j : ℕ) + 1 < 3 := by omega
    simp [e6SCols, hj3, hk3, hk, Matrix.mulVec_mulVec, pow_succ']
  intro j hj
  by_cases hj2 : (j : ℕ) < 2
  · obtain ⟨k, hk⟩ : ∃ k : Fin Tag.E6.rank, (k : ℕ) = (j : ℕ) + 1 :=
      ⟨⟨(j : ℕ) + 1, by have : Tag.E6.rank = 6 := rfl; omega⟩, rfl⟩
    rw [hstep j k hj2 hk]
    exact hmem k (by omega)
  · have hj2' : (j : ℕ) = 2 := by omega
    have hjeq : e6SCols s δ j = (e6SM δ ^ 2) *ᵥ e6F4Col s := by
      simp [e6SCols, hj2']
    rw [hjeq, Matrix.mulVec_mulVec, ← pow_succ', e6S_pow_col_three s hs δ hδ]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.sub_mem _ m2 m1) m0)

theorem e6S_card_ne_zero {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {q : ℕ} (hq : 2 ≤ q) :
    ((q : ℤ) ^ 3 - δ * (q : ℤ) ^ 2 + (q : ℤ) - δ).natAbs ≠ 0 := by
  have := e6SP_eval_ne_zero hδ hq
  rw [e6SP_eval] at this
  exact Int.natAbs_ne_zero.2 this

theorem e6S_block_cyclic (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples (e6SM δ) Fr
        (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) ∧
      Nat.card (fixedBlockTuples (e6SM δ) Fr
        (e6SCols s δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) =
          ((q : ℤ) ^ 3 - δ * (q : ℤ) ^ 2 + (q : ℤ) - δ).natAbs := by
  have hs3 : s + 3 = 0 ∨ s + 3 = 3 := by rcases hs with rfl | rfl <;> decide
  have h := isCyclic_and_card_fixedBlockTuples (L := L) (e6SM δ) (e6SCols s δ) (k := 3)
    (by decide) (e6F4Col (s + 3)) (e6SCols_basis s hs δ hδ).1 (e6SCols_basis s hs δ hδ).2
    (fun j hj => by
      have hj3 : ¬ (j : ℕ) < 3 := by omega
      simp [e6SCols, hj3])
    (e6S_stab s hs δ hδ) (e6SP δ) (e6SP_monic δ)
    (by rw [e6SP_natDegree]; rfl)
    (by rw [e6S_P_col (s + 3) hs3 δ hδ]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (by rcases hδ with rfl | rfl <;> simp [e6SP_coeff_zero])
    (e6SP_eval_ne_zero hδ hq)
  refine ⟨h.1, ?_⟩
  rw [h.2, e6SP_eval]

theorem e6S_inf_eq_bot (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] (Fr : L →+* L) :
    fixedBlockTuples (e6SM δ) Fr (e6SCols 3 δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ⊓
      fixedBlockTuples (e6SM δ) Fr
        (e6SCols 0 δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  obtain ⟨a3_0, a3_1, a3_2⟩ := e6S_first_block_mem 3 (Or.inr rfl) δ hδ
  obtain ⟨a0_0, a0_1, a0_2⟩ := e6S_first_block_mem 0 (Or.inl rfl) δ hδ
  have hS : ∀ u ∈ Set.range e6F4Col, rootChar a u = 1 := by
    rintro _ ⟨k, rfl⟩
    have h3 := (mem_fixedBlockTuples.1 ha1).2
    have h0 := (mem_fixedBlockTuples.1 ha2).2
    fin_cases k
    · exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_0
    · exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_1
    · exact CTTorus.rootChar_eq_one_of_mem_span h0 a0_2
    · exact CTTorus.rootChar_eq_one_of_mem_span h3 a3_0
    · exact CTTorus.rootChar_eq_one_of_mem_span h3 a3_1
    · exact CTTorus.rootChar_eq_one_of_mem_span h3 a3_2
  have h1 : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u => by
    refine CTTorus.rootChar_eq_one_of_mem_span hS ?_
    rw [e6F4Col_basis.2]
    exact Submodule.mem_top
  exact h1 ▸ Subgroup.one_mem _

theorem e6S_card_sup (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {L : Type} [Field L] [IsAlgClosed L]
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    Nat.card ↥(fixedBlockTuples (e6SM δ) Fr
        (e6SCols 3 δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ⊔
      fixedBlockTuples (e6SM δ) Fr
        (e6SCols 0 δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) =
      ((q : ℤ) ^ 3 - δ * (q : ℤ) ^ 2 + (q : ℤ) - δ).natAbs ^ 2 := by
  obtain ⟨-, h3⟩ := e6S_block_cyclic 3 (Or.inr rfl) δ hδ Fr hFr hℓ hℓq hq
  obtain ⟨-, h0⟩ := e6S_block_cyclic 0 (Or.inl rfl) δ hδ Fr hFr hℓ hℓq hq
  have hne := e6S_card_ne_zero hδ hq
  have : Finite ↥(fixedBlockTuples (e6SM δ) Fr
      (e6SCols 3 δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) :=
    Nat.finite_of_card_ne_zero (by rw [h3]; exact hne)
  have : Finite ↥(fixedBlockTuples (e6SM δ) Fr
      (e6SCols 0 δ '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) :=
    Nat.finite_of_card_ne_zero (by rw [h0]; exact hne)
  rw [card_sup_of_inf_eq_bot_E6 (e6S_inf_eq_bot δ hδ Fr), h3, h0]
  exact (sq _).symm

theorem e6S_rootChar_col {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {a : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e6SM δ) Fr) (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) :
    rootChar a (e6F4Col (o + 1)) = (rootChar a (e6F4Col o) ^ q) ^ δ ∧
      rootChar a (e6F4Col (o + 2)) = rootChar a (e6F4Col o) ^ (q ^ 2) := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  constructor
  · have h := rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha 1 (e6F4Col o)
    rw [e6S_pow_col_one o ho, rootChar_zsmul, pow_one] at h
    calc rootChar a (e6F4Col (o + 1))
        = (rootChar a (e6F4Col (o + 1)) ^ δ) ^ δ := by rw [← zpow_mul, hδ2, zpow_one]
      _ = (rootChar a (e6F4Col o) ^ q) ^ δ := by rw [h]
  · have h := rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha 2 (e6F4Col o)
    rwa [e6S_pow_col_two o ho δ hδ] at h

theorem e6S_values_injective {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) {a a' : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e6SM δ) Fr) (ha' : a' ∈ fixedCharTuples (e6SM δ) Fr)
    (h1 : rootChar a e6F4V = rootChar a' e6F4V)
    (h2 : rootChar a (e6F4C • e6F4V) = rootChar a' (e6F4C • e6F4V)) : a = a' := by
  obtain ⟨c1, c2⟩ := e6S_rootChar_col Fr hFr hδ ha 0 (Or.inl rfl)
  obtain ⟨c4, c5⟩ := e6S_rootChar_col Fr hFr hδ ha 3 (Or.inr rfl)
  obtain ⟨d1, d2⟩ := e6S_rootChar_col Fr hFr hδ ha' 0 (Or.inl rfl)
  obtain ⟨d4, d5⟩ := e6S_rootChar_col Fr hFr hδ ha' 3 (Or.inr rfl)
  have e0 : rootChar a (e6F4Col 0) = rootChar a' (e6F4Col 0) := h1
  have e3 : rootChar a (e6F4Col 3) = rootChar a' (e6F4Col 3) := h2
  have hcols : ∀ k : Fin Tag.E6.rank, rootChar a (e6F4Col k) = rootChar a' (e6F4Col k) := by
    intro k
    fin_cases k
    · exact e0
    · exact c1.trans ((congrArg (fun x => (x ^ q) ^ δ) e0).trans d1.symm)
    · exact c2.trans ((congrArg (· ^ q ^ 2) e0).trans d2.symm)
    · exact e3
    · exact c4.trans ((congrArg (fun x => (x ^ q) ^ δ) e3).trans d4.symm)
    · exact c5.trans ((congrArg (· ^ q ^ 2) e3).trans d5.symm)
  have hall : ∀ u, rootChar a u = rootChar a' u := fun u => by
    have hu : u ∈ Submodule.span ℤ (Set.range e6F4Col) := by
      rw [e6F4Col_basis.2]
      exact Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hcols k
    | zero => rw [rootChar_zero, rootChar_zero]
    | add x y _ _ hx hy => rw [rootChar_add, rootChar_add, hx, hy]
    | smul n x _ hx => rw [rootChar_zsmul, rootChar_zsmul, hx]
  funext i
  rw [← CTTorus.rootChar_single a i, ← CTTorus.rootChar_single a' i, hall]

theorem e6S_card_two_torsion_le_four {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    {Γ : Subgroup (Fin Tag.E6.rank → Lˣ)} (hΓ : Γ ≤ fixedCharTuples (e6SM δ) Fr) :
    Finite {a : Γ // a ^ 2 = 1} ∧ Nat.card {a : Γ // a ^ 2 = 1} ≤ 4 := by
  have hsq : ∀ a : Γ, a ^ 2 = 1 → ∀ u, rootChar (a : Fin Tag.E6.rank → Lˣ) u ^ 2 = 1 := by
    intro a ha u
    refine CTTorus.rootChar_pow_eq_one (p := 2) (fun i => ?_) u
    have h := congrFun (congrArg Subtype.val ha) i
    simpa using h
  let φ : {a : Γ // a ^ 2 = 1} → rootsOfUnity 2 L × rootsOfUnity 2 L := fun a =>
    (⟨rootChar (a.1 : Fin Tag.E6.rank → Lˣ) e6F4V, (mem_rootsOfUnity 2 _).2 (hsq a.1 a.2 _)⟩,
      ⟨rootChar (a.1 : Fin Tag.E6.rank → Lˣ) (e6F4C • e6F4V),
        (mem_rootsOfUnity 2 _).2 (hsq a.1 a.2 _)⟩)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : rootChar (a.1 : Fin Tag.E6.rank → Lˣ) e6F4V =
        rootChar (b.1 : Fin Tag.E6.rank → Lˣ) e6F4V :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => ((x.1 : Lˣ))) hab
    have h2 : rootChar (a.1 : Fin Tag.E6.rank → Lˣ) (e6F4C • e6F4V) =
        rootChar (b.1 : Fin Tag.E6.rank → Lˣ) (e6F4C • e6F4V) :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => ((x.2 : Lˣ))) hab
    exact Subtype.ext (Subtype.ext
      (e6S_values_injective Fr hFr hδ (hΓ a.1.2) (hΓ b.1.2) h1 h2))
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  calc Nat.card {a : Γ // a ^ 2 = 1}
      ≤ Nat.card (rootsOfUnity 2 L × rootsOfUnity 2 L) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 2 L) * Nat.card (rootsOfUnity 2 L) := Nat.card_prod _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul (card_rootsOfUnity L 2) (card_rootsOfUnity L 2)
    _ = 4 := rfl

theorem e6S_eigencolumn_neg {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (e6SM (-1)) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 ∧
      (dualMatrix (ZMod p) e6F4U).mulVec z = (-(q : ZMod p)) • z ∧
        rootCharKernel a = rootKernel z := by
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (e6SM (-1)) Fr hFr hp ha hap ha1
  exact ⟨z, hz0, transpose_eigen_neg (weylMatrix e6F4U) (q : ZMod p) z hzM, hzk⟩

end CFSG.RankThree.PartOne.KE
