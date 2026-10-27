module

public import CFSG.RankThree.PartOne.KE.CTBlock
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFour

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal dualMatrix weylMatrix weylMatrix_mulVec weylMatrix_pow)
open scoped Matrix Polynomial

@[expose] def e6FourM : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := weylMatrix e6F4U

@[expose] def e6F4Col (j : Fin Tag.E6.rank) : Fin Tag.E6.rank → ℤ := fun i => e6F4B i j

theorem e6FourM_pow_mulVec (i : ℕ) (x : Fin Tag.E6.rank → ℤ) :
    (e6FourM ^ i) *ᵥ x = (e6F4U ^ i) • x := by
  rw [e6FourM, ← weylMatrix_pow, weylMatrix_mulVec]

open Polynomial in
@[expose] def e6FourP : ℤ[X] :=
  X ^ 3 - X ^ 2 + X - 1

theorem e6FourP_monic : e6FourP.Monic := by
  unfold e6FourP
  monicity!

theorem e6FourP_natDegree : e6FourP.natDegree = 3 := by
  unfold e6FourP
  compute_degree!

theorem e6FourP_coeff_zero : e6FourP.coeff 0 = -1 := by
  simp [e6FourP, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow]

theorem e6FourP_eval (q : ℤ) : e6FourP.eval q = q ^ 3 - q ^ 2 + q - 1 := by
  simp [e6FourP]

theorem e6FourP_eval_ne_zero {q : ℕ} (hq : 2 ≤ q) : e6FourP.eval (q : ℤ) ≠ 0 := by
  rw [e6FourP_eval]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have h : (q : ℤ) ^ 3 - (q : ℤ) ^ 2 + (q : ℤ) - 1 = ((q : ℤ) - 1) * ((q : ℤ) ^ 2 + 1) := by ring
  rw [h]
  exact mul_ne_zero (by omega) (by positivity)

theorem aeval_e6FourP :
    Polynomial.aeval e6FourM e6FourP = e6FourM ^ 3 - e6FourM ^ 2 + e6FourM - 1 := by
  simp [e6FourP]

open Polynomial in
theorem aeval_e6FourP_eq_mul :
    Polynomial.aeval e6FourM e6FourP = (e6FourM ^ 2 + 1) * (e6FourM - 1) := by
  have h : e6FourP = (X ^ 2 + 1) * (X - 1) := by
    unfold e6FourP
    ring
  rw [h]
  simp

theorem e6F4Col_eq : e6F4Col 0 = e6F4V ∧ e6F4Col 1 = e6F4U • e6F4V ∧
    e6F4Col 2 = (e6F4U ^ 2) • e6F4V ∧ e6F4Col 3 = e6F4C • e6F4V ∧
    e6F4Col 4 = e6F4U • e6F4C • e6F4V ∧ e6F4Col 5 = (e6F4U ^ 2) • e6F4C • e6F4V :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem e6F4U_cols :
    e6F4U • e6F4Col 0 = e6F4Col 1 ∧ (e6F4U ^ 2) • e6F4Col 0 = e6F4Col 2 ∧
      e6F4U • e6F4Col 3 = e6F4Col 4 ∧ (e6F4U ^ 2) • e6F4Col 3 = e6F4Col 5 := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := e6F4Col_eq
  rw [c0, c1, c2, c3, c4, c5]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem e6Four_pow_col_one (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) :
    (e6FourM ^ 1) *ᵥ e6F4Col o = e6F4Col (o + 1) := by
  rw [e6FourM_pow_mulVec, pow_one]
  rcases ho with rfl | rfl
  · rw [zero_add]
    exact e6F4U_cols.1
  · exact e6F4U_cols.2.2.1

theorem e6Four_pow_col_two (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) :
    (e6FourM ^ 2) *ᵥ e6F4Col o = e6F4Col (o + 2) := by
  rw [e6FourM_pow_mulVec]
  rcases ho with rfl | rfl
  · rw [zero_add]
    exact e6F4U_cols.2.1
  · exact e6F4U_cols.2.2.2

theorem card_sup_of_inf_eq_bot_E6 {G : Type*} [CommGroup G] {A B : Subgroup G} [Finite A]
    [Finite B] (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
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

theorem e6Four_P_col (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) :
    (Polynomial.aeval e6FourM e6FourP) *ᵥ e6F4Col o = 0 := by
  rw [aeval_e6FourP_eq_mul]
  rcases ho with rfl | rfl
  · exact e6F4_kills _ (Or.inl rfl)
  · exact e6F4_kills _ (Or.inr rfl)

theorem e6Four_pow_col_three (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) :
    (e6FourM ^ 3) *ᵥ e6F4Col o = e6F4Col (o + 2) - e6F4Col (o + 1) + e6F4Col o := by
  have h := e6Four_P_col o ho
  have h1 := e6Four_pow_col_one o ho
  rw [pow_one] at h1
  have h2 := e6Four_pow_col_two o ho
  rw [aeval_e6FourP] at h
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, h1, h2] at h
  calc (e6FourM ^ 3) *ᵥ e6F4Col o
      = ((e6FourM ^ 3) *ᵥ e6F4Col o - e6F4Col (o + 2) + e6F4Col (o + 1) - e6F4Col o) +
        (e6F4Col (o + 2) - e6F4Col (o + 1) + e6F4Col o) := by abel
    _ = e6F4Col (o + 2) - e6F4Col (o + 1) + e6F4Col o := by rw [h, zero_add]

theorem e6F4Col_basis :
    LinearIndependent ℤ e6F4Col ∧ Submodule.span ℤ (Set.range e6F4Col) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E6.rank)), Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.E6.rank)).toMatrix e6F4Col =
      Matrix.of fun i j => e6F4Col j i := rfl
  have h' : (Matrix.of fun i j => e6F4Col j i) = e6F4B := rfl
  rw [h, h', e6F4B_det]
  exact isUnit_one.neg

@[expose] def e6FourCols (s : Fin Tag.E6.rank) : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  fun j =>
    if (j : ℕ) < 3 then (e6FourM ^ (j : ℕ)) *ᵥ e6F4Col s
    else (e6FourM ^ ((j : ℕ) - 3)) *ᵥ e6F4Col (s + 3)

theorem e6FourCols_eq (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) (j : Fin Tag.E6.rank) :
    e6FourCols s j = e6F4Col (j + s) := by
  have hs3 : s + 3 = 0 ∨ s + 3 = 3 := by rcases hs with rfl | rfl <;> decide
  have p1 := e6Four_pow_col_one s hs
  have p2 := e6Four_pow_col_two s hs
  have q1 := e6Four_pow_col_one (s + 3) hs3
  have q2 := e6Four_pow_col_two (s + 3) hs3
  have hr6 : Tag.E6.rank = 6 := rfl
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : e6FourCols s 0 = (e6FourM ^ 0) *ᵥ e6F4Col s := by simp [e6FourCols, hr6]
    rw [e, pow_zero, Matrix.one_mulVec, zero_add]
  · have e : e6FourCols s 1 = (e6FourM ^ 1) *ᵥ e6F4Col s := by simp [e6FourCols, hr6]
    rw [e, p1, add_comm s 1]
  · have e : e6FourCols s 2 = (e6FourM ^ 2) *ᵥ e6F4Col s := by simp [e6FourCols, hr6]
    rw [e, p2, add_comm s 2]
  · have e : e6FourCols s 3 = (e6FourM ^ 0) *ᵥ e6F4Col (s + 3) := by simp [e6FourCols, hr6]
    rw [e, pow_zero, Matrix.one_mulVec, add_comm s 3]
  · have e : e6FourCols s 4 = (e6FourM ^ 1) *ᵥ e6F4Col (s + 3) := by simp [e6FourCols, hr6]
    rw [e, q1, show (4 : Fin Tag.E6.rank) + s = s + 3 + 1 by
      rcases hs with rfl | rfl <;> decide]
  · have e : e6FourCols s 5 = (e6FourM ^ 2) *ᵥ e6F4Col (s + 3) := by simp [e6FourCols, hr6]
    rw [e, q2, show (5 : Fin Tag.E6.rank) + s = s + 3 + 2 by
      rcases hs with rfl | rfl <;> decide]

theorem e6FourCols_basis (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) :
    LinearIndependent ℤ (e6FourCols s) ∧ Submodule.span ℤ (Set.range (e6FourCols s)) = ⊤ := by
  have h : e6FourCols s = e6F4Col ∘ fun j => j + s := funext (e6FourCols_eq s hs)
  rw [h]
  refine ⟨e6F4Col_basis.1.comp _ (add_left_injective s), ?_⟩
  rw [Set.range_comp, (add_right_surjective s).range_eq, Set.image_univ]
  exact e6F4Col_basis.2

theorem e6Four_first_block_mem (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) :
    e6F4Col s ∈ Submodule.span ℤ (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ∧
      e6F4Col (s + 1) ∈
        Submodule.span ℤ (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ∧
      e6F4Col (s + 2) ∈
        Submodule.span ℤ (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := by
  have hmem : ∀ i : Fin Tag.E6.rank, (i : ℕ) < 3 →
      e6F4Col (i + s) ∈ Submodule.span ℤ
        (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := fun i hi =>
    Submodule.subset_span ⟨i, hi, e6FourCols_eq s hs i⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := hmem 0 (by decide)
    rwa [zero_add] at h
  · have h := hmem 1 (by decide)
    rwa [add_comm 1 s] at h
  · have h := hmem 2 (by decide)
    rwa [add_comm 2 s] at h

theorem e6Four_stab (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) :
    ∀ j : Fin Tag.E6.rank, (j : ℕ) < 3 →
      e6FourM *ᵥ e6FourCols s j ∈
        Submodule.span ℤ (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) := by
  obtain ⟨m0, m1, m2⟩ := e6Four_first_block_mem s hs
  have b1 := e6Four_pow_col_one s hs
  rw [pow_one] at b1
  have b2 : e6FourM *ᵥ e6F4Col (s + 1) = e6F4Col (s + 2) := by
    calc e6FourM *ᵥ e6F4Col (s + 1) = e6FourM *ᵥ (e6FourM *ᵥ e6F4Col s) := by rw [b1]
      _ = (e6FourM ^ 2) *ᵥ e6F4Col s := by rw [Matrix.mulVec_mulVec, ← sq]
      _ = e6F4Col (s + 2) := e6Four_pow_col_two s hs
  have b3 : e6FourM *ᵥ e6F4Col (s + 2) = e6F4Col (s + 2) - e6F4Col (s + 1) + e6F4Col s := by
    calc e6FourM *ᵥ e6F4Col (s + 2) = e6FourM *ᵥ ((e6FourM ^ 2) *ᵥ e6F4Col s) := by
          rw [e6Four_pow_col_two s hs]
      _ = (e6FourM ^ 3) *ᵥ e6F4Col s := by rw [Matrix.mulVec_mulVec, ← pow_succ']
      _ = e6F4Col (s + 2) - e6F4Col (s + 1) + e6F4Col s := e6Four_pow_col_three s hs
  intro j hj
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by
    rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rw [e6FourCols_eq s hs j]
  rcases hj3 with rfl | rfl | rfl
  · rw [zero_add, b1]
    exact m1
  · rw [add_comm 1 s, b2]
    exact m2
  · rw [add_comm 2 s, b3]
    exact Submodule.add_mem _ (Submodule.sub_mem _ m2 m1) m0

theorem e6Four_card_ne_zero {q : ℕ} (hq : 2 ≤ q) :
    ((q : ℤ) ^ 3 - (q : ℤ) ^ 2 + (q : ℤ) - 1).natAbs ≠ 0 := by
  have := e6FourP_eval_ne_zero hq
  rw [e6FourP_eval] at this
  exact Int.natAbs_ne_zero.2 this

theorem e6Four_block_cyclic (s : Fin Tag.E6.rank) (hs : s = 0 ∨ s = 3) {L : Type} [Field L]
    [IsAlgClosed L] (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ]
    (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples e6FourM Fr
        (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) ∧
      Nat.card (fixedBlockTuples e6FourM Fr
        (e6FourCols s '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) =
          ((q : ℤ) ^ 3 - (q : ℤ) ^ 2 + (q : ℤ) - 1).natAbs := by
  have hs3 : s + 3 = 0 ∨ s + 3 = 3 := by rcases hs with rfl | rfl <;> decide
  have h := isCyclic_and_card_fixedBlockTuples (L := L) e6FourM (e6FourCols s) (k := 3)
    (by decide) (e6F4Col (s + 3)) (e6FourCols_basis s hs).1 (e6FourCols_basis s hs).2
    (fun j hj => by
      have hj3 : ¬ (j : ℕ) < 3 := by omega
      simp [e6FourCols, hj3])
    (e6Four_stab s hs) e6FourP e6FourP_monic
    (by rw [e6FourP_natDegree]; rfl)
    (by rw [e6Four_P_col (s + 3) hs3]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (Or.inr e6FourP_coeff_zero) (e6FourP_eval_ne_zero hq)
  refine ⟨h.1, ?_⟩
  rw [h.2, e6FourP_eval]

theorem e6Four_inf_eq_bot {L : Type} [Field L] (Fr : L →+* L) :
    fixedBlockTuples e6FourM Fr (e6FourCols 3 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ⊓
      fixedBlockTuples e6FourM Fr (e6FourCols 0 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  obtain ⟨a3_0, a3_1, a3_2⟩ := e6Four_first_block_mem 3 (Or.inr rfl)
  obtain ⟨a0_0, a0_1, a0_2⟩ := e6Four_first_block_mem 0 (Or.inl rfl)
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

theorem e6Four_eigencolumn {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e6FourM Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 ∧
      (dualMatrix (ZMod p) e6F4U).mulVec z = (q : ZMod p) • z ∧
        rootCharKernel a = rootKernel z := by
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples e6FourM Fr hFr hp ha hap ha1
  exact ⟨z, hz0, hzM, hzk⟩

theorem e6Four_card_sup {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    Nat.card ↥(fixedBlockTuples e6FourM Fr
        (e6FourCols 3 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3}) ⊔
      fixedBlockTuples e6FourM Fr
        (e6FourCols 0 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) =
      ((q : ℤ) ^ 3 - (q : ℤ) ^ 2 + (q : ℤ) - 1).natAbs ^ 2 := by
  obtain ⟨-, h3⟩ := e6Four_block_cyclic 3 (Or.inr rfl) Fr hFr hℓ hℓq hq
  obtain ⟨-, h0⟩ := e6Four_block_cyclic 0 (Or.inl rfl) Fr hFr hℓ hℓq hq
  have hne := e6Four_card_ne_zero hq
  have : Finite ↥(fixedBlockTuples e6FourM Fr
      (e6FourCols 3 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) :=
    Nat.finite_of_card_ne_zero (by rw [h3]; exact hne)
  have : Finite ↥(fixedBlockTuples e6FourM Fr
      (e6FourCols 0 '' {i : Fin Tag.E6.rank | (i : ℕ) < 3})) :=
    Nat.finite_of_card_ne_zero (by rw [h0]; exact hne)
  rw [card_sup_of_inf_eq_bot_E6 (e6Four_inf_eq_bot Fr), h3, h0]
  exact (sq _).symm

theorem e6Four_rootChar_col {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e6FourM Fr) (o : Fin Tag.E6.rank) (ho : o = 0 ∨ o = 3) :
    rootChar a (e6F4Col (o + 1)) = rootChar a (e6F4Col o) ^ q ∧
      rootChar a (e6F4Col (o + 2)) = rootChar a (e6F4Col o) ^ (q ^ 2) := by
  constructor
  · have h := rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha 1 (e6F4Col o)
    rw [e6Four_pow_col_one o ho, pow_one] at h
    exact h
  · have h := rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha 2 (e6F4Col o)
    rwa [e6Four_pow_col_two o ho] at h

theorem e6Four_values_injective {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a a' : Fin Tag.E6.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e6FourM Fr) (ha' : a' ∈ fixedCharTuples e6FourM Fr)
    (h1 : rootChar a e6F4V = rootChar a' e6F4V)
    (h2 : rootChar a (e6F4C • e6F4V) = rootChar a' (e6F4C • e6F4V)) : a = a' := by
  obtain ⟨c1, c2⟩ := e6Four_rootChar_col Fr hFr ha 0 (Or.inl rfl)
  obtain ⟨c4, c5⟩ := e6Four_rootChar_col Fr hFr ha 3 (Or.inr rfl)
  obtain ⟨d1, d2⟩ := e6Four_rootChar_col Fr hFr ha' 0 (Or.inl rfl)
  obtain ⟨d4, d5⟩ := e6Four_rootChar_col Fr hFr ha' 3 (Or.inr rfl)
  have e0 : rootChar a (e6F4Col 0) = rootChar a' (e6F4Col 0) := h1
  have e3 : rootChar a (e6F4Col 3) = rootChar a' (e6F4Col 3) := h2
  have hcols : ∀ k : Fin Tag.E6.rank, rootChar a (e6F4Col k) = rootChar a' (e6F4Col k) := by
    intro k
    fin_cases k
    · exact e0
    · exact c1.trans ((congrArg (· ^ q) e0).trans d1.symm)
    · exact c2.trans ((congrArg (· ^ q ^ 2) e0).trans d2.symm)
    · exact e3
    · exact c4.trans ((congrArg (· ^ q) e3).trans d4.symm)
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

theorem e6Four_card_two_torsion_le_four {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {Γ : Subgroup (Fin Tag.E6.rank → Lˣ)}
    (hΓ : Γ ≤ fixedCharTuples e6FourM Fr) :
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
      (e6Four_values_injective Fr hFr (hΓ a.1.2) (hΓ b.1.2) h1 h2))
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  calc Nat.card {a : Γ // a ^ 2 = 1}
      ≤ Nat.card (rootsOfUnity 2 L × rootsOfUnity 2 L) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 2 L) * Nat.card (rootsOfUnity 2 L) := Nat.card_prod _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul (card_rootsOfUnity L 2) (card_rootsOfUnity L 2)
    _ = 4 := rfl

end CFSG.RankThree.PartOne.KE
