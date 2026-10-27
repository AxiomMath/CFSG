module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private noncomputable def permConjClosure {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (I : Finset (Fin d)) (p : ℕ) :
    Subgroup ↥(unitarySU 2 n K d) :=
  Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
    (fun x : ↥(unitarySU 2 n K d) => permSU hK σ * x * (permSU hK σ)⁻¹) ''
      {x : ↥(unitarySU 2 n K d) | x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
        (∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        ∃ k : ℕ, x ^ p ^ k = 1})

private theorem norm_one_ne_zero {K : Type} [Field K] {n : ℕ} {μ : K}
    (hμ : μ ^ (2 ^ n + 1) = 1) : μ ≠ 0 := by
  intro h0
  rw [h0, zero_pow (Nat.succ_ne_zero (2 ^ n))] at hμ
  exact zero_ne_one hμ

private noncomputable def pairElem {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (a b : Fin d) (μ : K)
    (hμ : μ ^ (2 ^ n + 1) = 1) : ↥(unitarySU 2 n K d) :=
  Classical.choose (LineU.exists_diagSU (u := TypeA.ggPairVec a b μ) hK
    (LineU.ggPairVec_norm_one hμ a b) (TypeA.prod_ggPairVec μ (norm_one_ne_zero hμ)))

private theorem coe_pairElem {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (a b : Fin d) (μ : K) (hμ : μ ^ (2 ^ n + 1) = 1) :
    ((pairElem hK a b μ hμ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (TypeA.ggPairVec a b μ) :=
  Classical.choose_spec (LineU.exists_diagSU (u := TypeA.ggPairVec a b μ) hK
    (LineU.ggPairVec_norm_one hμ a b) (TypeA.prod_ggPairVec μ (norm_one_ne_zero hμ)))

private theorem pairElem_pow_eq_one {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (a b : Fin d) (μ : K) (hμ : μ ^ (2 ^ n + 1) = 1)
    {N : ℕ} (hμN : μ ^ N = 1) : pairElem hK a b μ hμ ^ N = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one,
    coe_pairElem, Matrix.diagonal_pow]
  rw [show TypeA.ggPairVec a b μ ^ N = (1 : Fin d → K) by
    funext m
    show TypeA.ggPairVec a b μ m ^ N = 1
    rw [TypeA.ggPairVec_apply, mul_pow]
    by_cases h1 : m = a
    · rw [if_pos h1]
      by_cases h2 : m = b
      · rw [if_pos h2]; simp [hμN, inv_pow]
      · rw [if_neg h2]; simp [hμN, inv_pow]
    · rw [if_neg h1]
      by_cases h2 : m = b
      · rw [if_pos h2]; simp [hμN, inv_pow]
      · rw [if_neg h2]; simp [hμN, inv_pow]]
  exact Matrix.diagonal_one

private theorem pairElem_mem_blockSU {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) {I : Finset (Fin d)} {a b : Fin d}
    (ha : a ∈ I) (hb : b ∈ I) (μ : K) (hμ : μ ^ (2 ^ n + 1) = 1) :
    pairElem hK a b μ hμ ∈ TableBUE.blockSU (K := K) (n := n) I := by
  rw [TableBUE.mem_blockSU, coe_pairElem]
  intro i j hij
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, TypeA.ggPairVec_apply]
    have hia : i ≠ a := by
      rintro rfl
      exact hij.elim (fun hi => hi ha) (fun hj => hj ha)
    have hib : i ≠ b := by
      rintro rfl
      exact hij.elim (fun hi => hi hb) (fun hj => hj hb)
    rw [if_neg hia, if_neg hib]
    simp
  · rw [if_neg h, if_neg h]

private theorem conj_pairElem {K : Type} [Field K] {n d : ℕ}
    (hK : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d)) (a b : Fin d) (μ : K)
    (hμ : μ ^ (2 ^ n + 1) = 1) :
    permSU hK σ * pairElem hK a b μ hμ * (permSU hK σ)⁻¹ =
      pairElem hK (σ a) (σ b) μ hμ := by
  apply Subtype.ext
  apply Units.ext
  rw [UnitAct.coe_permSU_conj hK (coe_pairElem hK a b μ hμ) σ, coe_pairElem]
  congr 1
  funext m
  have h := congrFun (TypeA.ggPairVec_comp_of (k := a) (l := b) (i := σ a) (j := σ b)
    rfl rfl μ) (σ.symm m)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h.symm

private theorem pairElem_mem_closure {K : Type} [Field K] {n d p : ℕ}
    (hK : UnitaryFieldData 2 n K) (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    {a b : Fin d} (hab : a ≠ b) (μ : K) (hμ : μ ^ (2 ^ n + 1) = 1)
    (hpμ : ∃ k, pairElem hK a b μ hμ ^ p ^ k = 1) :
    pairElem hK a b μ hμ ∈ permConjClosure hK I p := by
  obtain ⟨i₀, hi₀, j₀, hj₀, hij₀⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  obtain ⟨σ, hσa, hσb⟩ := TypeA.exists_perm_pair hij₀ hab
  have hconj : permSU hK σ * pairElem hK i₀ j₀ μ hμ * (permSU hK σ)⁻¹ =
      pairElem hK a b μ hμ := by
    rw [conj_pairElem hK σ i₀ j₀ μ hμ, hσa, hσb]
  have hxpow : ∃ k : ℕ, pairElem hK i₀ j₀ μ hμ ^ p ^ k = 1 := by
    obtain ⟨m, hm⟩ := hpμ
    refine ⟨m, ?_⟩
    have h2 : pairElem hK i₀ j₀ μ hμ =
        (permSU hK σ)⁻¹ * pairElem hK a b μ hμ * ((permSU hK σ)⁻¹)⁻¹ := by
      rw [← hconj]
      group
    rw [h2, conj_pow, hm]
    simp
  have hxblock : pairElem hK i₀ j₀ μ hμ ∈ TableBUE.blockSU (K := K) (n := n) I :=
    pairElem_mem_blockSU hK hi₀ hj₀ μ hμ
  have hxdiag : ∃ w : Fin d → K,
      ((pairElem hK i₀ j₀ μ hμ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w :=
    ⟨_, coe_pairElem hK i₀ j₀ μ hμ⟩
  have hy : permSU hK σ * pairElem hK i₀ j₀ μ hμ * (permSU hK σ)⁻¹ ∈
      (⋃ σ' : Equiv.Perm (Fin d),
        (fun x : ↥(unitarySU 2 n K d) => permSU hK σ' * x * (permSU hK σ')⁻¹) ''
          {x : ↥(unitarySU 2 n K d) | x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
            (∃ w : Fin d → K,
              ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w) ∧
            ∃ k : ℕ, x ^ p ^ k = 1}) :=
    Set.mem_iUnion.mpr ⟨σ, ⟨pairElem hK i₀ j₀ μ hμ, ⟨hxblock, hxdiag, hxpow⟩, rfl⟩⟩
  have hmem : permSU hK σ * pairElem hK i₀ j₀ μ hμ * (permSU hK σ)⁻¹ ∈
      permConjClosure hK I p := Subgroup.subset_closure hy
  rwa [hconj] at hmem

theorem diag_pElt_mem_closure_permConj
    {d n p : ℕ} {K : Type} [Field K] (hKd : UnitaryFieldData 2 n K)
    (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    (s : ↥(unitarySU 2 n K d))
    (hs : ∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    (hsp : ∃ k : ℕ, s ^ p ^ k = 1) :
    s ∈ Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
      (fun x => permSU hKd σ * x * (permSU hKd σ)⁻¹) ''
        {x : ↥(unitarySU 2 n K d) | x ∈ TableBUE.blockSU (K := K) (n := n) I ∧
          (∃ v : Fin d → K, ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
          ∃ k : ℕ, x ^ p ^ k = 1}) := by
  classical
  change s ∈ permConjClosure hKd I p
  obtain ⟨v, hv⟩ := hs
  obtain ⟨k, hk⟩ := hsp
  have hnorm : ∀ i, v i ^ (2 ^ n + 1) = 1 := by
    intro i
    have h1 : diagonal (fun i => hKd.bar (v i) * v i) = 1 := by
      have h2 := ((mem_unitarySU_iff hKd).mp s.2).2
      rwa [hv, Matrix.diagonal_map (map_zero hKd.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal] at h2
    have h3 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) h1
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h3
    rw [hKd.bar_apply, ← pow_succ] at h3
    exact h3
  have hprod : ∏ i, v i = 1 := by
    have h1 := ((mem_unitarySU_iff hKd).mp s.2).1
    rwa [hv, Matrix.det_diagonal] at h1
  have hv0 : ∀ i, v i ≠ 0 := fun i => norm_one_ne_zero (hnorm i)
  have hvpow : ∀ i, v i ^ p ^ k = 1 := by
    intro i
    have h1 : (diagonal v) ^ p ^ k = 1 := by
      have h2 := congrArg (fun x : ↥(unitarySU 2 n K d) =>
        ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val,
        Units.val_one, hv] using h2
    have h2 : diagonal (v ^ p ^ k) = 1 := by
      rwa [Matrix.diagonal_pow] at h1
    have h3 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) h2
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.pow_apply] using h3
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  have hFex : ∀ k' : Fin d, ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (TypeA.ggPairVec k' i₀ (v k')) := by
    intro k'
    exact LineU.exists_diagSU (u := TypeA.ggPairVec k' i₀ (v k')) hKd
      (LineU.ggPairVec_norm_one (hnorm k') k' i₀)
      (TypeA.prod_ggPairVec (v k') (hv0 k'))
  choose F hF using hFex
  have hFi : F i₀ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hF i₀, Subgroup.coe_one, Units.val_one]
    congr 1
    funext m
    rw [TypeA.ggPairVec_apply]
    by_cases h : m = i₀
    · simp [h, hv0 i₀]
    · simp [h]
  have hFmem : ∀ k' : Fin d, F k' ∈ permConjClosure hKd I p := by
    intro k'
    by_cases hk' : k' = i₀
    · rw [hk', hFi]
      exact Subgroup.one_mem _
    · have hFP : F k' = pairElem hKd k' i₀ (v k') (hnorm k') := by
        apply Subtype.ext
        apply Units.ext
        rw [hF k', coe_pairElem]
      rw [hFP]
      exact pairElem_mem_closure hKd I hI hk' (v k') (hnorm k')
        ⟨k, pairElem_pow_eq_one hKd k' i₀ (v k') (hnorm k') (hvpow k')⟩
  have hfun : (∏ k', TypeA.ggPairVec k' i₀ (v k')) = v := by
    funext m
    rw [Finset.prod_apply]
    simp only [TypeA.ggPairVec_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq Finset.univ m v,
      ite_eq_left (Finset.mem_univ m)]
    by_cases hm : m = i₀
    · simp only [hm, ite_true, Finset.prod_inv_distrib]
      rw [hprod, inv_one, mul_one]
    · simp [hm]
  let M : Submonoid (Fin d → K) :=
    { carrier := {u | ∃ D : ↥(unitarySU 2 n K d), D ∈ permConjClosure hKd I p ∧
        ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u}
      one_mem' := ⟨1, Subgroup.one_mem _,
        by rw [Subgroup.coe_one, Units.val_one]; exact Matrix.diagonal_one.symm⟩
      mul_mem' := by
        rintro u w ⟨Du, hDu, hDu'⟩ ⟨Dw, hDw, hDw'⟩
        refine ⟨Du * Dw, Subgroup.mul_mem _ hDu hDw, ?_⟩
        rw [Subgroup.coe_mul, Units.val_mul, hDu', hDw', Matrix.diagonal_mul_diagonal]
        rfl }
  have hvM : v ∈ M := by
    have hmem : (∏ k', TypeA.ggPairVec k' i₀ (v k')) ∈ M :=
      M.prod_mem (fun k' _ => ⟨F k', hFmem k', hF k'⟩)
    rwa [hfun] at hmem
  obtain ⟨D, hD, hDv⟩ := hvM
  have hDs : D = s := by
    apply Subtype.ext
    apply Units.ext
    rw [hDv, hv]
  rw [← hDs]
  exact hD

end CFSG.StandardType
