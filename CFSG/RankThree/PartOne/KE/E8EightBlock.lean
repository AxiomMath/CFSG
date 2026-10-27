module

public import CFSG.RankThree.PartOne.KE.E8EightLattice
public import CFSG.RankThree.PartOne.KE.E8FiveBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem e8T8V_relation : e8T8V ^ 4 + 1 = 0 := by
  have hL : ladd Tag.E8.rank (lpow Tag.E8.rank e8T8VList 4) (lid Tag.E8.rank) =
      lofFn Tag.E8.rank (fun _ _ => 0) := by
    decide +kernel
  have h := congrArg (toMat Tag.E8.rank) hL
  rw [toMat_ladd, toMat_lpow, toMat_lid, ← e8T8V_eq, toMat_lofFn] at h
  exact h

@[expose] def e8T8Bas (x y : List ℤ) : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := fun j =>
  toVec Tag.E8.rank ((lorbit Tag.E8.rank e8T8VList x 4 ++ lorbit Tag.E8.rank e8T8VList y 4).getD
    (j : ℕ) [])

theorem e8T8Bas_lt {x y : List ℤ} {j : Fin Tag.E8.rank} (hj : (j : ℕ) < 4) :
    e8T8Bas x y j = (e8T8V ^ (j : ℕ)) *ᵥ toVec Tag.E8.rank x := by
  have h : (lorbit Tag.E8.rank e8T8VList x 4 ++ lorbit Tag.E8.rank e8T8VList y 4).getD
      (j : ℕ) [] = (lorbit Tag.E8.rank e8T8VList x 4).getD (j : ℕ) [] :=
    List.getD_append _ _ _ _ (by simp [lorbit]; omega)
  rw [e8T8Bas, h, toVec_lorbit_getD hj, e8T8V_eq]

theorem e8T8Bas_ge {x y : List ℤ} {j : Fin Tag.E8.rank} (hj : 4 ≤ (j : ℕ)) :
    e8T8Bas x y j = (e8T8V ^ ((j : ℕ) - 4)) *ᵥ toVec Tag.E8.rank y := by
  have hj8 : (j : ℕ) < 8 := j.isLt
  have h : (lorbit Tag.E8.rank e8T8VList x 4 ++ lorbit Tag.E8.rank e8T8VList y 4).getD
      (j : ℕ) [] = (lorbit Tag.E8.rank e8T8VList y 4).getD ((j : ℕ) - 4) [] := by
    rw [List.getD_append_right _ _ _ _ (by simp [lorbit]; omega)]
    simp [lorbit]
  rw [e8T8Bas, h, toVec_lorbit_getD (by omega), e8T8V_eq]

theorem e8T8Bas_basis {x y : List ℤ}
    (hdet : (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList x 4 ++
      lorbit Tag.E8.rank e8T8VList y 4))).det = -1 ∨
      (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList x 4 ++
      lorbit Tag.E8.rank e8T8VList y 4))).det = 1) :
    LinearIndependent ℤ (e8T8Bas x y) ∧ Submodule.span ℤ (Set.range (e8T8Bas x y)) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E8.rank)), Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.E8.rank)).toMatrix (e8T8Bas x y) =
      toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList x 4 ++
        lorbit Tag.E8.rank e8T8VList y 4)) := by
    rw [toMat_lcols]
    rfl
  rw [h]
  rcases hdet with h | h <;> rw [h]
  · exact isUnit_one.neg
  · exact isUnit_one

open Polynomial in
theorem e8T8_block_cyclic {x y : List ℤ}
    (hdet : (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList x 4 ++
      lorbit Tag.E8.rank e8T8VList y 4))).det = -1 ∨
      (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList x 4 ++
      lorbit Tag.E8.rank e8T8VList y 4))).det = 1)
    {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    IsCyclic (fixedBlockTuples e8T8V Fr (e8T8Bas x y '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) ∧
      Nat.card (fixedBlockTuples e8T8V Fr
        (e8T8Bas x y '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) = q ^ 4 + 1 := by
  have hPmonic : (X ^ 4 + 1 : ℤ[X]).Monic := by
    have h : (X ^ 4 + 1 : ℤ[X]) = X ^ 4 + C 1 := by simp
    rw [h]
    exact Polynomial.monic_X_pow_add_C 1 (by norm_num)
  have hPdeg : (X ^ 4 + 1 : ℤ[X]).natDegree = Tag.E8.rank - 4 := by
    have h : (X ^ 4 + 1 : ℤ[X]).natDegree = 4 := by
      compute_degree!
    rw [h]
    rfl
  have hcoeff : (X ^ 4 + 1 : ℤ[X]).coeff 0 = 1 := by
    simp [Polynomial.coeff_one]
  have hne : (X ^ 4 + 1 : ℤ[X]).eval (q : ℤ) ≠ 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    positivity
  have haeval : Polynomial.aeval e8T8V (X ^ 4 + 1 : ℤ[X]) = 0 := by
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    exact e8T8V_relation
  have hbasis := e8T8Bas_basis hdet
  have hrank : Tag.E8.rank = 8 := rfl
  have h4 : e8T8V ^ 4 = -1 := by
    have h := e8T8V_relation
    calc e8T8V ^ 4 = (e8T8V ^ 4 + 1) + (-1) := by abel
      _ = -1 := by rw [h, zero_add]
  have hmem : ∀ i : ℕ, i < 4 → (e8T8V ^ i) *ᵥ toVec Tag.E8.rank x ∈
      Submodule.span ℤ (e8T8Bas x y '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) := by
    intro i hi
    have h := e8T8Bas_lt (x := x) (y := y) (j := ⟨i, by omega⟩) (by simpa using hi)
    rw [← h]
    exact Submodule.subset_span ⟨_, by simpa using hi, rfl⟩
  have h := isCyclic_and_card_fixedBlockTuples (L := L) e8T8V (e8T8Bas x y) (k := 4)
    (by decide) (toVec Tag.E8.rank y) hbasis.1 hbasis.2
    (fun j hj => e8T8Bas_ge hj)
    (fun j hj => by
      have hj4 : (j : ℕ) < 4 := hj
      rw [e8T8Bas_lt hj4, Matrix.mulVec_mulVec, ← pow_succ']
      by_cases hj3 : (j : ℕ) < 3
      · exact hmem _ (by omega)
      · have hj3' : (j : ℕ) = 3 := by omega
        rw [hj3', h4, Matrix.neg_mulVec, Matrix.one_mulVec]
        exact Submodule.neg_mem _ (by simpa using hmem 0 (by norm_num)))
    (X ^ 4 + 1) hPmonic hPdeg
    (by rw [haeval, Matrix.zero_mulVec]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (Or.inl hcoeff) hne
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  have e : (q : ℤ) ^ 4 + 1 = ((q ^ 4 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.natAbs_natCast]

theorem e8T8_detA :
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList e8T12B1List 4 ++
      lorbit Tag.E8.rank e8T8VList e8T12B2List 4))).det = -1 ∨
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList e8T12B1List 4 ++
      lorbit Tag.E8.rank e8T8VList e8T12B2List 4))).det = 1 :=
  Or.inl e8T8Cols_det

theorem e8T8_detB :
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList e8T12B2List 4 ++
      lorbit Tag.E8.rank e8T8VList e8T12B1List 4))).det = -1 ∨
    (toMat Tag.E8.rank (lcols Tag.E8.rank (lorbit Tag.E8.rank e8T8VList e8T12B2List 4 ++
      lorbit Tag.E8.rank e8T8VList e8T12B1List 4))).det = 1 := by
  rw [det_toMat_eq]
  decide +kernel

theorem e8T8_inf_eq_bot {L : Type} [Field L] (Fr : L →+* L) :
    fixedBlockTuples e8T8V Fr
        (e8T8Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ⊓
      fixedBlockTuples e8T8V Fr
        (e8T8Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  have h1 := (mem_fixedBlockTuples.1 ha1).2
  have h2 := (mem_fixedBlockTuples.1 ha2).2
  have hS : ∀ u ∈ Set.range (e8T8Bas e8T12B1List e8T12B2List), rootChar a u = 1 := by
    rintro _ ⟨j, rfl⟩
    by_cases hj : (j : ℕ) < 4
    · exact h1 _ ⟨j, hj, rfl⟩
    · have hj4 : 4 ≤ (j : ℕ) := by omega
      have hj8 : (j : ℕ) < 8 := j.isLt
      have e : e8T8Bas e8T12B1List e8T12B2List j =
          e8T8Bas e8T12B2List e8T12B1List ⟨(j : ℕ) - 4, by omega⟩ := by
        rw [e8T8Bas_ge hj4, e8T8Bas_lt (by simp; omega)]
      rw [e]
      exact h2 _ ⟨⟨(j : ℕ) - 4, by omega⟩, by simp; omega, rfl⟩
  have h1' : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u => by
    refine CTTorus.rootChar_eq_one_of_mem_span hS ?_
    rw [(e8T8Bas_basis e8T8_detA).2]
    exact Submodule.mem_top
  exact h1' ▸ Subgroup.one_mem _

theorem e8T8_card_sup {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    Nat.card ↥(fixedBlockTuples e8T8V Fr
        (e8T8Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) ⊔
      fixedBlockTuples e8T8V Fr
        (e8T8Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) =
      (q ^ 4 + 1) ^ 2 := by
  obtain ⟨-, h1⟩ := e8T8_block_cyclic e8T8_detA Fr hFr hℓ hℓq
  obtain ⟨-, h2⟩ := e8T8_block_cyclic e8T8_detB Fr hFr hℓ hℓq
  have hne : q ^ 4 + 1 ≠ 0 := by positivity
  have : Finite ↥(fixedBlockTuples e8T8V Fr
      (e8T8Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact hne)
  have : Finite ↥(fixedBlockTuples e8T8V Fr
      (e8T8Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4})) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hne)
  rw [card_sup_of_inf_eq_bot (e8T8_inf_eq_bot Fr), h1, h2]
  exact (sq _).symm

theorem e8T8_values_injective {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a a' : Fin Tag.E8.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e8T8V Fr) (ha' : a' ∈ fixedCharTuples e8T8V Fr)
    (h1 : rootChar a (toVec Tag.E8.rank e8T12B1List) = rootChar a' (toVec Tag.E8.rank e8T12B1List))
    (h2 : rootChar a (toVec Tag.E8.rank e8T12B2List) = rootChar a' (toVec Tag.E8.rank e8T12B2List)) :
    a = a' := by
  have hcols : ∀ j : Fin Tag.E8.rank, rootChar a (e8T8Bas e8T12B1List e8T12B2List j) =
      rootChar a' (e8T8Bas e8T12B1List e8T12B2List j) := by
    intro j
    by_cases hj : (j : ℕ) < 4
    · rw [e8T8Bas_lt hj, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha,
        rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha', h1]
    · have hj4 : 4 ≤ (j : ℕ) := by omega
      rw [e8T8Bas_ge hj4, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha,
        rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha', h2]
  have hall : ∀ u, rootChar a u = rootChar a' u := fun u => by
    have hu : u ∈ Submodule.span ℤ (Set.range (e8T8Bas e8T12B1List e8T12B2List)) := by
      rw [(e8T8Bas_basis e8T8_detA).2]
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

theorem e8T8_card_two_torsion_le_four {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {Γ : Subgroup (Fin Tag.E8.rank → Lˣ)}
    (hΓ : Γ ≤ fixedCharTuples e8T8V Fr) :
    Finite {a : Γ // a ^ 2 = 1} ∧ Nat.card {a : Γ // a ^ 2 = 1} ≤ 4 := by
  have hsq : ∀ a : Γ, a ^ 2 = 1 → ∀ u, rootChar (a : Fin Tag.E8.rank → Lˣ) u ^ 2 = 1 := by
    intro a ha u
    refine CTTorus.rootChar_pow_eq_one (p := 2) (fun i => ?_) u
    have h := congrFun (congrArg Subtype.val ha) i
    simpa using h
  let φ : {a : Γ // a ^ 2 = 1} → rootsOfUnity 2 L × rootsOfUnity 2 L := fun a =>
    (⟨rootChar (a.1 : Fin Tag.E8.rank → Lˣ) (toVec Tag.E8.rank e8T12B1List),
        (mem_rootsOfUnity 2 _).2 (hsq a.1 a.2 _)⟩,
      ⟨rootChar (a.1 : Fin Tag.E8.rank → Lˣ) (toVec Tag.E8.rank e8T12B2List),
        (mem_rootsOfUnity 2 _).2 (hsq a.1 a.2 _)⟩)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : rootChar (a.1 : Fin Tag.E8.rank → Lˣ) (toVec Tag.E8.rank e8T12B1List) =
        rootChar (b.1 : Fin Tag.E8.rank → Lˣ) (toVec Tag.E8.rank e8T12B1List) :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => ((x.1 : Lˣ))) hab
    have h2 : rootChar (a.1 : Fin Tag.E8.rank → Lˣ) (toVec Tag.E8.rank e8T12B2List) =
        rootChar (b.1 : Fin Tag.E8.rank → Lˣ) (toVec Tag.E8.rank e8T12B2List) :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => ((x.2 : Lˣ))) hab
    exact Subtype.ext (Subtype.ext
      (e8T8_values_injective Fr hFr (hΓ a.1.2) (hΓ b.1.2) h1 h2))
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  calc Nat.card {a : Γ // a ^ 2 = 1}
      ≤ Nat.card (rootsOfUnity 2 L × rootsOfUnity 2 L) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 2 L) * Nat.card (rootsOfUnity 2 L) := Nat.card_prod _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul (card_rootsOfUnity L 2) (card_rootsOfUnity L 2)
    _ = 4 := rfl

end CFSG.RankThree.PartOne.KE
