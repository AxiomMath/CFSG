module

public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.E8FiveBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem e7F4_rel1 : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank e7T12VList =
    toVec Tag.E7.rank e7T12BetaList - toVec Tag.E7.rank e7T12AlphaList := by
  have hL : lmulVec Tag.E7.rank (ladd Tag.E7.rank (lpow Tag.E7.rank e7F4WList 2)
      (lid Tag.E7.rank)) e7T12VList =
        vadd Tag.E7.rank e7T12BetaList (vneg Tag.E7.rank e7T12AlphaList) := by
    decide +kernel
  have h := congrArg (toVec Tag.E7.rank) hL
  rw [toVec_lmulVec, toMat_ladd, toMat_lpow, toMat_lid, ← e7F4W_eq, toVec_vadd,
    toVec_vneg] at h
  rw [sub_eq_add_neg]
  exact h

theorem e7F4_rel2 : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank e7F4B2List =
    toVec Tag.E7.rank e7T12GammaList - toVec Tag.E7.rank e7T12BetaList := by
  have hL : lmulVec Tag.E7.rank (ladd Tag.E7.rank (lpow Tag.E7.rank e7F4WList 2)
      (lid Tag.E7.rank)) e7F4B2List =
        vadd Tag.E7.rank e7T12GammaList (vneg Tag.E7.rank e7T12BetaList) := by
    decide +kernel
  have h := congrArg (toVec Tag.E7.rank) hL
  rw [toVec_lmulVec, toMat_ladd, toMat_lpow, toMat_lid, ← e7F4W_eq, toVec_vadd,
    toVec_vneg] at h
  rw [sub_eq_add_neg]
  exact h

@[expose] def e7F4Bas (x y : List ℤ) : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ := fun j =>
  toVec Tag.E7.rank ((e7F4FList ++ (lorbit Tag.E7.rank e7F4WList x 2 ++
    lorbit Tag.E7.rank e7F4WList y 2)).getD (j : ℕ) [])

theorem e7F4Bas_F {x y : List ℤ} {j : Fin Tag.E7.rank} (hj : (j : ℕ) < 3) :
    e7F4Bas x y j = toVec Tag.E7.rank (e7F4FList.getD (j : ℕ) []) := by
  rw [e7F4Bas, List.getD_append _ _ _ _ (by simp [e7F4FList]; omega)]

theorem e7F4Bas_mid {x y : List ℤ} {j : Fin Tag.E7.rank} (hj3 : 3 ≤ (j : ℕ)) (hj : (j : ℕ) < 5) :
    e7F4Bas x y j = (e7F4W ^ ((j : ℕ) - 3)) *ᵥ toVec Tag.E7.rank x := by
  rw [e7F4Bas, List.getD_append_right _ _ _ _ (by simp [e7F4FList]; omega)]
  have h4 : (j : ℕ) - e7F4FList.length = (j : ℕ) - 3 := by simp [e7F4FList]
  rw [h4, List.getD_append _ _ _ _ (by simp [lorbit]; omega), toVec_lorbit_getD (by omega),
    e7F4W_eq]

theorem e7F4Bas_hi {x y : List ℤ} {j : Fin Tag.E7.rank} (hj : 5 ≤ (j : ℕ)) :
    e7F4Bas x y j = (e7F4W ^ ((j : ℕ) - 5)) *ᵥ toVec Tag.E7.rank y := by
  have hj7 : (j : ℕ) < 7 := j.isLt
  rw [e7F4Bas, List.getD_append_right _ _ _ _ (by simp [e7F4FList]; omega)]
  have h4 : (j : ℕ) - e7F4FList.length = (j : ℕ) - 3 := by simp [e7F4FList]
  rw [h4, List.getD_append_right _ _ _ _ (by simp [lorbit]; omega)]
  have h6 : (j : ℕ) - 3 - (lorbit Tag.E7.rank e7F4WList x 2).length = (j : ℕ) - 5 := by
    simp [lorbit]
    omega
  rw [h6, toVec_lorbit_getD (by omega), e7F4W_eq]

theorem e7F4Bas_basis {x y : List ℤ}
    (hdet : (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList x 2 ++ lorbit Tag.E7.rank e7F4WList y 2)))).det = -1 ∨
      (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList x 2 ++ lorbit Tag.E7.rank e7F4WList y 2)))).det = 1) :
    LinearIndependent ℤ (e7F4Bas x y) ∧ Submodule.span ℤ (Set.range (e7F4Bas x y)) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E7.rank)), Module.Basis.det_apply]
  have h : (Pi.basisFun ℤ (Fin Tag.E7.rank)).toMatrix (e7F4Bas x y) =
      toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
        (lorbit Tag.E7.rank e7F4WList x 2 ++ lorbit Tag.E7.rank e7F4WList y 2))) := by
    rw [toMat_lcols]
    rfl
  rw [h]
  rcases hdet with h | h <;> rw [h]
  · exact isUnit_one.neg
  · exact isUnit_one

theorem e7F4_detA :
    (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList e7T12VList 2 ++
        lorbit Tag.E7.rank e7F4WList e7F4B2List 2)))).det = -1 ∨
    (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList e7T12VList 2 ++
        lorbit Tag.E7.rank e7F4WList e7F4B2List 2)))).det = 1 :=
  Or.inl e7F4Cols_det

theorem e7F4_detB :
    (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList e7F4B2List 2 ++
        lorbit Tag.E7.rank e7F4WList e7T12VList 2)))).det = -1 ∨
    (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList e7F4B2List 2 ++
        lorbit Tag.E7.rank e7F4WList e7T12VList 2)))).det = 1 := by
  rw [det_toMat_eq]
  decide +kernel

theorem e7F4_mulVec_F {x : List ℤ} (hx : x ∈ e7F4FList) :
    e7F4W *ᵥ toVec Tag.E7.rank x = toVec Tag.E7.rank x := by
  rw [e7F4W_eq, ← toVec_lmulVec, e7F4W_fixes x hx]

open Polynomial in
theorem e7F4_block_cyclic {x y : List ℤ}
    (hdet : (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList x 2 ++ lorbit Tag.E7.rank e7F4WList y 2)))).det = -1 ∨
      (toMat Tag.E7.rank (lcols Tag.E7.rank (e7F4FList ++
      (lorbit Tag.E7.rank e7F4WList x 2 ++ lorbit Tag.E7.rank e7F4WList y 2)))).det = 1)
    (hxrel : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank x ∈
      Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}))
    (hyrel : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank y ∈
      Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}))
    {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    IsCyclic (fixedBlockTuples e7F4W Fr (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5})) ∧
      Nat.card (fixedBlockTuples e7F4W Fr
        (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5})) = q ^ 2 + 1 := by
  have hPmonic : (X ^ 2 + 1 : ℤ[X]).Monic := by
    have h : (X ^ 2 + 1 : ℤ[X]) = X ^ 2 + C 1 := by simp
    rw [h]
    exact Polynomial.monic_X_pow_add_C 1 (by norm_num)
  have hPdeg : (X ^ 2 + 1 : ℤ[X]).natDegree = Tag.E7.rank - 5 := by
    have h : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
      compute_degree!
    rw [h]
    rfl
  have hcoeff : (X ^ 2 + 1 : ℤ[X]).coeff 0 = 1 := by
    simp [Polynomial.coeff_one]
  have hne : (X ^ 2 + 1 : ℤ[X]).eval (q : ℤ) ≠ 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    positivity
  have hbasis := e7F4Bas_basis hdet
  have hrank : Tag.E7.rank = 7 := rfl
  have hspanN : ∀ i : ℕ, i < 5 → ∀ j : Fin Tag.E7.rank, (j : ℕ) = i →
      e7F4Bas x y j ∈ Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) :=
    fun i hi j hj => Submodule.subset_span ⟨j, by simp [hj, hi], rfl⟩
  have hFN : ∀ f ∈ e7F4FList, toVec Tag.E7.rank f ∈
      Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) := by
    intro f hf
    have hlen : e7F4FList.length = 3 := rfl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have hj3 : j < 3 := hlen ▸ hj
    have h := hspanN j (by omega) ⟨j, by omega⟩ rfl
    rw [e7F4Bas_F (by simpa using hj3), List.getD_eq_getElem _ _ hj] at h
    exact h
  have hsubspan : Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) ≤
      Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) :=
    Submodule.span_mono (Set.image_mono fun i hi => by simp at hi ⊢; omega)
  have hx5 : toVec Tag.E7.rank x ∈
      Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) := by
    have h := hspanN 3 (by norm_num) ⟨3, by omega⟩ rfl
    rw [e7F4Bas_mid (by simp) (by simp)] at h
    simpa using h
  have hwx5 : e7F4W *ᵥ toVec Tag.E7.rank x ∈
      Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) := by
    have h := hspanN 4 (by norm_num) ⟨4, by omega⟩ rfl
    rw [e7F4Bas_mid (by simp) (by simp)] at h
    simpa using h
  have h := isCyclic_and_card_fixedBlockTuples (L := L) e7F4W (e7F4Bas x y) (k := 5)
    (by decide) (toVec Tag.E7.rank y) hbasis.1 hbasis.2
    (fun j hj => by
      have := e7F4Bas_hi (x := x) (y := y) hj
      rw [this])
    (fun j hj => by
      have hj5 : (j : ℕ) < 5 := hj
      by_cases hj3 : (j : ℕ) < 3
      · rw [e7F4Bas_F hj3]
        have hmem : e7F4FList.getD (j : ℕ) [] ∈ e7F4FList := by
          have hlen : (j : ℕ) < e7F4FList.length := by simp [e7F4FList]; omega
          rw [List.getD_eq_getElem _ _ hlen]
          exact List.getElem_mem hlen
        rw [e7F4_mulVec_F hmem]
        exact hFN _ hmem
      · by_cases hj4 : (j : ℕ) = 3
        · rw [e7F4Bas_mid (by omega) (by omega)]
          have hh : (j : ℕ) - 3 = 0 := by omega
          rw [hh, pow_zero, Matrix.one_mulVec]
          exact hwx5
        · have hj4' : (j : ℕ) = 4 := by omega
          rw [e7F4Bas_mid (by omega) (by omega)]
          have hh : (j : ℕ) - 3 = 1 := by omega
          rw [hh, pow_one, Matrix.mulVec_mulVec, ← pow_two]
          have h1 : (e7F4W ^ 2) *ᵥ toVec Tag.E7.rank x = (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank x -
              toVec Tag.E7.rank x := by
            rw [Matrix.add_mulVec, Matrix.one_mulVec]
            abel
          rw [h1]
          exact Submodule.sub_mem _ (hsubspan hxrel) hx5)
    (X ^ 2 + 1) hPmonic hPdeg
    (by
      have h2 : (Polynomial.aeval e7F4W (X ^ 2 + 1 : ℤ[X])) = e7F4W ^ 2 + 1 := by
        simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
      rw [h2]
      exact hsubspan hyrel)
    Fr hFr hℓ hℓq (Or.inl hcoeff) hne
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  have e : (q : ℤ) ^ 2 + 1 = ((q ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.natAbs_natCast]

theorem e7F4_F_mem_span (x y : List ℤ) : ∀ f ∈ e7F4FList, toVec Tag.E7.rank f ∈
    Submodule.span ℤ (e7F4Bas x y '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := by
  intro f hf
  have hlen : e7F4FList.length = 3 := rfl
  have hrank : Tag.E7.rank = 7 := rfl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  have hj3 : j < 3 := hlen ▸ hj
  refine Submodule.subset_span ⟨⟨j, by omega⟩, by simp [hj3], ?_⟩
  rw [e7F4Bas_F (by simpa using hj3), List.getD_eq_getElem _ _ hj]

theorem e7F4_xrelA : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank e7T12VList ∈
    Submodule.span ℤ (e7F4Bas e7T12VList e7F4B2List '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := by
  rw [e7F4_rel1]
  exact Submodule.sub_mem _ (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))
    (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))

theorem e7F4_yrelA : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank e7F4B2List ∈
    Submodule.span ℤ (e7F4Bas e7T12VList e7F4B2List '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := by
  rw [e7F4_rel2]
  exact Submodule.sub_mem _ (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))
    (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))

theorem e7F4_xrelB : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank e7F4B2List ∈
    Submodule.span ℤ (e7F4Bas e7F4B2List e7T12VList '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := by
  rw [e7F4_rel2]
  exact Submodule.sub_mem _ (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))
    (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))

theorem e7F4_yrelB : (e7F4W ^ 2 + 1) *ᵥ toVec Tag.E7.rank e7T12VList ∈
    Submodule.span ℤ (e7F4Bas e7F4B2List e7T12VList '' {i : Fin Tag.E7.rank | (i : ℕ) < 3}) := by
  rw [e7F4_rel1]
  exact Submodule.sub_mem _ (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))
    (e7F4_F_mem_span _ _ _ (by simp [e7F4FList]))

theorem e7F4_inf_eq_bot {L : Type} [Field L] (Fr : L →+* L) :
    fixedBlockTuples e7F4W Fr
        (e7F4Bas e7T12VList e7F4B2List '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) ⊓
      fixedBlockTuples e7F4W Fr
        (e7F4Bas e7F4B2List e7T12VList '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  have h1 := (mem_fixedBlockTuples.1 ha1).2
  have h2 := (mem_fixedBlockTuples.1 ha2).2
  have hS : ∀ u ∈ Set.range (e7F4Bas e7T12VList e7F4B2List), rootChar a u = 1 := by
    rintro _ ⟨j, rfl⟩
    by_cases hj : (j : ℕ) < 5
    · exact h1 _ ⟨j, hj, rfl⟩
    · have hj5 : 5 ≤ (j : ℕ) := by omega
      have hj7 : (j : ℕ) < 7 := j.isLt
      have e : e7F4Bas e7T12VList e7F4B2List j =
          e7F4Bas e7F4B2List e7T12VList ⟨(j : ℕ) - 2, by omega⟩ := by
        rw [e7F4Bas_hi hj5, e7F4Bas_mid (by simp; omega) (by simp; omega)]
        simp only
        congr 2
      rw [e]
      exact h2 _ ⟨⟨(j : ℕ) - 2, by omega⟩, by simp; omega, rfl⟩
  have h1' : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u => by
    refine CTTorus.rootChar_eq_one_of_mem_span hS ?_
    rw [(e7F4Bas_basis e7F4_detA).2]
    exact Submodule.mem_top
  exact h1' ▸ Subgroup.one_mem _

theorem e7F4_card_sup {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) :
    Nat.card ↥(fixedBlockTuples e7F4W Fr
        (e7F4Bas e7T12VList e7F4B2List '' {i : Fin Tag.E7.rank | (i : ℕ) < 5}) ⊔
      fixedBlockTuples e7F4W Fr
        (e7F4Bas e7F4B2List e7T12VList '' {i : Fin Tag.E7.rank | (i : ℕ) < 5})) =
      (q ^ 2 + 1) ^ 2 := by
  obtain ⟨-, h1⟩ := e7F4_block_cyclic e7F4_detA e7F4_xrelA e7F4_yrelA Fr hFr hℓ hℓq
  obtain ⟨-, h2⟩ := e7F4_block_cyclic e7F4_detB e7F4_xrelB e7F4_yrelB Fr hFr hℓ hℓq
  have hne : q ^ 2 + 1 ≠ 0 := by positivity
  have : Finite ↥(fixedBlockTuples e7F4W Fr
      (e7F4Bas e7T12VList e7F4B2List '' {i : Fin Tag.E7.rank | (i : ℕ) < 5})) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact hne)
  have : Finite ↥(fixedBlockTuples e7F4W Fr
      (e7F4Bas e7F4B2List e7T12VList '' {i : Fin Tag.E7.rank | (i : ℕ) < 5})) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hne)
  rw [card_sup_of_inf_eq_bot (e7F4_inf_eq_bot Fr), h1, h2]
  exact (sq _).symm

theorem e7F4_values_injective {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a a' : Fin Tag.E7.rank → Lˣ}
    (ha : a ∈ fixedCharTuples e7F4W Fr) (ha' : a' ∈ fixedCharTuples e7F4W Fr)
    (haF : ∀ f ∈ e7F4FList, rootChar a (toVec Tag.E7.rank f) = 1)
    (ha'F : ∀ f ∈ e7F4FList, rootChar a' (toVec Tag.E7.rank f) = 1)
    (h1 : rootChar a (toVec Tag.E7.rank e7T12VList) = rootChar a' (toVec Tag.E7.rank e7T12VList))
    (h2 : rootChar a (toVec Tag.E7.rank e7F4B2List) =
      rootChar a' (toVec Tag.E7.rank e7F4B2List)) :
    a = a' := by
  have hcols : ∀ j : Fin Tag.E7.rank, rootChar a (e7F4Bas e7T12VList e7F4B2List j) =
      rootChar a' (e7F4Bas e7T12VList e7F4B2List j) := by
    intro j
    by_cases hj3 : (j : ℕ) < 3
    · rw [e7F4Bas_F hj3]
      have hmem : e7F4FList.getD (j : ℕ) [] ∈ e7F4FList := by
        have hlen : (j : ℕ) < e7F4FList.length := by simp [e7F4FList]; omega
        rw [List.getD_eq_getElem _ _ hlen]
        exact List.getElem_mem hlen
      rw [haF _ hmem, ha'F _ hmem]
    · by_cases hj5 : (j : ℕ) < 5
      · rw [e7F4Bas_mid (by omega) hj5, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha,
          rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha', h1]
      · rw [e7F4Bas_hi (by omega), rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha,
          rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha', h2]
  have hall : ∀ u, rootChar a u = rootChar a' u := fun u => by
    have hu : u ∈ Submodule.span ℤ (Set.range (e7F4Bas e7T12VList e7F4B2List)) := by
      rw [(e7F4Bas_basis e7F4_detA).2]
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

theorem e7F4_card_two_torsion_le_four {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {Γ : Subgroup (Fin Tag.E7.rank → Lˣ)}
    (hΓ : Γ ≤ fixedCharTuples e7F4W Fr)
    (hΓF : ∀ a ∈ Γ, ∀ f ∈ e7F4FList, rootChar a (toVec Tag.E7.rank f) = 1) :
    Finite {a : Γ // a ^ 2 = 1} ∧ Nat.card {a : Γ // a ^ 2 = 1} ≤ 4 := by
  have hsq : ∀ a : Γ, a ^ 2 = 1 → ∀ u, rootChar (a : Fin Tag.E7.rank → Lˣ) u ^ 2 = 1 := by
    intro a ha u
    refine CTTorus.rootChar_pow_eq_one (p := 2) (fun i => ?_) u
    have h := congrFun (congrArg Subtype.val ha) i
    simpa using h
  let φ : {a : Γ // a ^ 2 = 1} → rootsOfUnity 2 L × rootsOfUnity 2 L := fun a =>
    (⟨rootChar (a.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7T12VList),
        (mem_rootsOfUnity 2 _).2 (hsq a.1 a.2 _)⟩,
      ⟨rootChar (a.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7F4B2List),
        (mem_rootsOfUnity 2 _).2 (hsq a.1 a.2 _)⟩)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : rootChar (a.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7T12VList) =
        rootChar (b.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7T12VList) :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => ((x.1 : Lˣ))) hab
    have h2 : rootChar (a.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7F4B2List) =
        rootChar (b.1 : Fin Tag.E7.rank → Lˣ) (toVec Tag.E7.rank e7F4B2List) :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => ((x.2 : Lˣ))) hab
    exact Subtype.ext (Subtype.ext
      (e7F4_values_injective Fr hFr (hΓ a.1.2) (hΓ b.1.2) (hΓF _ a.1.2) (hΓF _ b.1.2) h1 h2))
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  calc Nat.card {a : Γ // a ^ 2 = 1}
      ≤ Nat.card (rootsOfUnity 2 L × rootsOfUnity 2 L) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 2 L) * Nat.card (rootsOfUnity 2 L) := Nat.card_prod _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul (card_rootsOfUnity L 2) (card_rootsOfUnity L 2)
    _ = 4 := rfl

end CFSG.RankThree.PartOne.KE
