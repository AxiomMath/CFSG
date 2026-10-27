module

public import CFSG.RankThree.PartOne.KE.E8TwelveLattice
public import CFSG.RankThree.PartOne.KE.E8FiveBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem e8T12V_relation : e8T12V ^ 4 - e8T12V ^ 2 + 1 = 0 := by
  have hL : ladd Tag.E8.rank (ladd Tag.E8.rank (lpow Tag.E8.rank e8T12VList 4)
      (lsmul Tag.E8.rank (-1) (lpow Tag.E8.rank e8T12VList 2))) (lid Tag.E8.rank) =
        lofFn Tag.E8.rank (fun _ _ => 0) := by
    decide +kernel
  have h := congrArg (toMat Tag.E8.rank) hL
  rw [toMat_ladd, toMat_ladd, toMat_lsmul, toMat_lpow, toMat_lpow, toMat_lid, ← e8T12V_eq,
    toMat_lofFn, neg_one_smul] at h
  rw [sub_eq_add_neg]
  exact h

@[expose] def e8T12Bas (x y : List ℤ) : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := fun j =>
  toVec Tag.E8.rank ((lorbit Tag.E8.rank e8T12VList x 4 ++ lorbit Tag.E8.rank e8T12VList y 4).getD
    (j : ℕ) [])

theorem e8T12Bas_lt {x y : List ℤ} {j : Fin Tag.E8.rank} (hj : (j : ℕ) < 4) :
    e8T12Bas x y j = (e8T12V ^ (j : ℕ)) *ᵥ toVec Tag.E8.rank x := by
  have h : (lorbit Tag.E8.rank e8T12VList x 4 ++ lorbit Tag.E8.rank e8T12VList y 4).getD
      (j : ℕ) [] = (lorbit Tag.E8.rank e8T12VList x 4).getD (j : ℕ) [] :=
    List.getD_append _ _ _ _ (by simp [lorbit]; omega)
  rw [e8T12Bas, h, toVec_lorbit_getD hj, e8T12V_eq]

theorem e8T12Bas_ge {x y : List ℤ} {j : Fin Tag.E8.rank} (hj : 4 ≤ (j : ℕ)) :
    e8T12Bas x y j = (e8T12V ^ ((j : ℕ) - 4)) *ᵥ toVec Tag.E8.rank y := by
  have hj8 : (j : ℕ) < 8 := j.isLt
  have h : (lorbit Tag.E8.rank e8T12VList x 4 ++ lorbit Tag.E8.rank e8T12VList y 4).getD
      (j : ℕ) [] = (lorbit Tag.E8.rank e8T12VList y 4).getD ((j : ℕ) - 4) [] := by
    rw [List.getD_append_right _ _ _ _ (by simp [lorbit]; omega)]
    simp [lorbit]
  rw [e8T12Bas, h, toVec_lorbit_getD (by omega), e8T12V_eq]

theorem e8T12Bas_basis {x y : List ℤ}
    (hdet : (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList x 4 ++
      lorbit Tag.E8.rank e8T12VList y 4))).det = -1 ∨
      (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList x 4 ++
      lorbit Tag.E8.rank e8T12VList y 4))).det = 1) :
    LinearIndependent ℤ (e8T12Bas x y) ∧ Submodule.span ℤ (Set.range (e8T12Bas x y)) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E8.rank)), Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.E8.rank)).toMatrix (e8T12Bas x y) =
      toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList x 4 ++
        lorbit Tag.E8.rank e8T12VList y 4)) := by
    rw [toMat_lcols]
    rfl
  rw [h]
  rcases hdet with h | h <;> rw [h]
  · exact isUnit_one.neg
  · exact isUnit_one

open Polynomial in
theorem e8T12_block_cyclic {x y : List ℤ}
    (hdet : (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList x 4 ++
      lorbit Tag.E8.rank e8T12VList y 4))).det = -1 ∨
      (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList x 4 ++
      lorbit Tag.E8.rank e8T12VList y 4))).det = 1)
    {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    IsCyclic (fixedBlockTuples e8T12V Fr (e8T12Bas x y '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) ∧
      Nat.card (fixedBlockTuples e8T12V Fr
        (e8T12Bas x y '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) = q ^ 4 - q ^ 2 + 1 := by
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
  have hPdeg : (X ^ 4 - X ^ 2 + 1 : ℤ[X]).natDegree = Tag.E8.rank - 4 := by
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
  have haeval : Polynomial.aeval e8T12V (X ^ 4 - X ^ 2 + 1 : ℤ[X]) = 0 := by
    simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, map_one]
    exact e8T12V_relation
  have hbasis := e8T12Bas_basis hdet
  have hrank : Tag.E8.rank = 8 := rfl
  have h4 : e8T12V ^ 4 = e8T12V ^ 2 - 1 := by
    have h := e8T12V_relation
    calc e8T12V ^ 4 = (e8T12V ^ 4 - e8T12V ^ 2 + 1) + (e8T12V ^ 2 - 1) := by abel
      _ = e8T12V ^ 2 - 1 := by rw [h, zero_add]
  have hmem : ∀ i : ℕ, i < 4 → (e8T12V ^ i) *ᵥ toVec Tag.E8.rank x ∈
      Submodule.span ℤ (e8T12Bas x y '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) := by
    intro i hi
    have h := e8T12Bas_lt (x := x) (y := y) (j := ⟨i, by omega⟩) (by simpa using hi)
    rw [← h]
    exact Submodule.subset_span ⟨_, by simpa using hi, rfl⟩
  have h := isCyclic_and_card_fixedBlockTuples (L := L) e8T12V (e8T12Bas x y) (k := 4)
    (by decide) (toVec Tag.E8.rank y) hbasis.1 hbasis.2
    (fun j hj => e8T12Bas_ge hj)
    (fun j hj => by
      have hj4 : (j : ℕ) < 4 := hj
      rw [e8T12Bas_lt hj4, Matrix.mulVec_mulVec, ← pow_succ']
      by_cases hj3 : (j : ℕ) < 3
      · exact hmem _ (by omega)
      · have hj3' : (j : ℕ) = 3 := by omega
        rw [hj3', h4, Matrix.sub_mulVec, Matrix.one_mulVec]
        exact Submodule.sub_mem _ (hmem 2 (by norm_num)) (by simpa using hmem 0 (by norm_num)))
    (X ^ 4 - X ^ 2 + 1) hPmonic hPdeg
    (by rw [haeval, Matrix.zero_mulVec]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (Or.inl hcoeff) hne
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

theorem e8T12_detA :
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList e8T12B1List 4 ++
      lorbit Tag.E8.rank e8T12VList e8T12B2List 4))).det = -1 ∨
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList e8T12B1List 4 ++
      lorbit Tag.E8.rank e8T12VList e8T12B2List 4))).det = 1 :=
  Or.inl e8T12Cols_det

theorem e8T12_detB :
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList e8T12B2List 4 ++
      lorbit Tag.E8.rank e8T12VList e8T12B1List 4))).det = -1 ∨
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T12VList e8T12B2List 4 ++
      lorbit Tag.E8.rank e8T12VList e8T12B1List 4))).det = 1 := by
  rw [det_toMat_eq]
  decide +kernel

theorem e8T12_inf_eq_bot {L : Type} [Field L] (Fr : L →+* L) :
    fixedBlockTuples e8T12V Fr
        (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ⊓
      fixedBlockTuples e8T12V Fr
        (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  have h1 := (mem_fixedBlockTuples.1 ha1).2
  have h2 := (mem_fixedBlockTuples.1 ha2).2
  have hS : ∀ u ∈ Set.range (e8T12Bas e8T12B1List e8T12B2List), rootChar a u = 1 := by
    rintro _ ⟨j, rfl⟩
    by_cases hj : (j : ℕ) < 4
    · exact h1 _ ⟨j, hj, rfl⟩
    · have hj4 : 4 ≤ (j : ℕ) := by omega
      have hj8 : (j : ℕ) < 8 := j.isLt
      have e : e8T12Bas e8T12B1List e8T12B2List j =
          e8T12Bas e8T12B2List e8T12B1List ⟨(j : ℕ) - 4, by omega⟩ := by
        rw [e8T12Bas_ge hj4, e8T12Bas_lt (by simp; omega)]
      rw [e]
      exact h2 _ ⟨⟨(j : ℕ) - 4, by omega⟩, by simp; omega, rfl⟩
  have h1' : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u => by
    refine CTTorus.rootChar_eq_one_of_mem_span hS ?_
    rw [(e8T12Bas_basis e8T12_detA).2]
    exact Submodule.mem_top
  exact h1' ▸ Subgroup.one_mem _

theorem e8T12_card_sup {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    Nat.card ↥(fixedBlockTuples e8T12V Fr
        (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ⊔
      fixedBlockTuples e8T12V Fr
        (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) =
      (q ^ 4 - q ^ 2 + 1) ^ 2 := by
  obtain ⟨-, h1⟩ := e8T12_block_cyclic e8T12_detA Fr hFr hℓ hℓq
  obtain ⟨-, h2⟩ := e8T12_block_cyclic e8T12_detB Fr hFr hℓ hℓq
  have hne : q ^ 4 - q ^ 2 + 1 ≠ 0 := by have := hq; omega
  have : Finite ↥(fixedBlockTuples e8T12V Fr
      (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact hne)
  have : Finite ↥(fixedBlockTuples e8T12V Fr
      (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hne)
  rw [card_sup_of_inf_eq_bot (e8T12_inf_eq_bot Fr), h1, h2]
  exact (sq _).symm

theorem e8T12_zpow_eq_one {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e8T12V Fr) (i : Fin Tag.E8.rank) :
    a i ^ ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) = 1 := by
  have h := rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr ha
    (Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 : ℤ[X]) (Pi.single i 1)
  have haeval : Polynomial.aeval e8T12V (Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 : ℤ[X]) = 0 := by
    simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, map_one]
    exact e8T12V_relation
  rw [haeval, Matrix.zero_mulVec, rootChar_zero, CTTorus.rootChar_single] at h
  simpa using h.symm

theorem e8T12_orderOf_dvd {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e8T12V Fr) (hq : 2 ≤ q) :
    orderOf a ∣ q ^ 4 - q ^ 2 + 1 := by
  apply orderOf_dvd_of_pow_eq_one
  funext i
  have h := e8T12_zpow_eq_one Fr hFr ha i
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq) (by norm_num)
  have e : (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 = ((q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h24]
    ring
  rw [e, zpow_natCast] at h
  rw [Pi.pow_apply, Pi.one_apply]
  exact h

end CFSG.RankThree.PartOne.KE
