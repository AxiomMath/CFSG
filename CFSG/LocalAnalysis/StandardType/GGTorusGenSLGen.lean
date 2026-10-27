module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private noncomputable def permConjClosureSL {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    (I : Finset (Fin d)) : Subgroup (SpecialLinearGroup (Fin d) K) :=
  Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
    (fun x : SpecialLinearGroup (Fin d) K => TypeA.permSL σ * x * (TypeA.permSL σ)⁻¹) ''
      {x : SpecialLinearGroup (Fin d) K |
        x ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I ∧
        (∃ v : Fin d → K, (x : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        ∃ k : ℕ, x ^ p ^ k = 1})

private noncomputable def pairElem {d : ℕ} {K : Type} [Field K]
    (a b : Fin d) (μ : K) (hμ : μ ≠ 0) : SpecialLinearGroup (Fin d) K :=
  ⟨diagonal (TypeA.ggPairVec a b μ), by
    rw [Matrix.det_diagonal]
    exact TypeA.prod_ggPairVec μ hμ⟩

private theorem coe_pairElem {d : ℕ} {K : Type} [Field K]
    (a b : Fin d) (μ : K) (hμ : μ ≠ 0) :
    ((pairElem a b μ hμ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (TypeA.ggPairVec a b μ) := rfl

private theorem pairElem_self {d : ℕ} {K : Type} [Field K]
    (a : Fin d) (μ : K) (hμ : μ ≠ 0) : pairElem a a μ hμ = 1 := by
  apply Subtype.ext
  rw [coe_pairElem, Matrix.SpecialLinearGroup.coe_one]
  have hfun : TypeA.ggPairVec a a μ = (1 : Fin d → K) := by
    funext m
    rw [TypeA.ggPairVec_apply]
    by_cases h : m = a
    · rw [if_pos h, if_pos h, mul_inv_cancel₀ hμ]
      simp
    · rw [if_neg h, if_neg h, one_mul]
      simp
  rw [hfun]
  exact Matrix.diagonal_one

private theorem pairElem_pow_eq_one {d : ℕ} {K : Type} [Field K]
    (a b : Fin d) (μ : K) (hμ : μ ≠ 0) {N : ℕ} (hμN : μ ^ N = 1) :
    pairElem a b μ hμ ^ N = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    coe_pairElem, Matrix.diagonal_pow]
  have hfun : TypeA.ggPairVec a b μ ^ N = (1 : Fin d → K) := by
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
      · rw [if_neg h2]; simp [hμN, inv_pow]
  rw [hfun]
  exact Matrix.diagonal_one

private theorem pairElem_mem_blockSpecialLinear {d : ℕ} {K : Type} [Field K]
    {I : Finset (Fin d)} {a b : Fin d} (ha : a ∈ I) (hb : b ∈ I)
    (μ : K) (hμ : μ ≠ 0) :
    pairElem a b μ hμ ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I := by
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
  intro i j hij
  rw [coe_pairElem, Matrix.diagonal_apply, Matrix.one_apply]
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

private theorem conj_pairElem {d : ℕ} {K : Type} [Field K] [CharP K 2]
    (σ : Equiv.Perm (Fin d)) (a b : Fin d) (μ : K) (hμ : μ ≠ 0) :
    TypeA.permSL σ * pairElem a b μ hμ * (TypeA.permSL σ)⁻¹ =
      pairElem (σ.symm a) (σ.symm b) μ hμ := by
  apply Subtype.ext
  rw [TypeA.coe_permSL_conj (coe_pairElem a b μ hμ) σ, coe_pairElem]
  congr 1
  exact TypeA.ggPairVec_comp a b μ σ

private theorem pairElem_mem_closure {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    {a b : Fin d} (hab : a ≠ b) (μ : K) (hμ : μ ≠ 0)
    (hpμ : ∃ k, pairElem a b μ hμ ^ p ^ k = 1) :
    pairElem a b μ hμ ∈ permConjClosureSL (p := p) I := by
  obtain ⟨i₀, hi₀, j₀, hj₀, hij₀⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  obtain ⟨σ', hσ'a, hσ'b⟩ := TypeA.exists_perm_pair hij₀ hab
  let σ : Equiv.Perm (Fin d) := σ'⁻¹
  have hσsymm : σ.symm = σ' := rfl
  have hconj : TypeA.permSL σ * pairElem i₀ j₀ μ hμ * (TypeA.permSL σ)⁻¹ =
      pairElem a b μ hμ := by
    rw [conj_pairElem σ i₀ j₀ μ hμ, hσsymm, hσ'a, hσ'b]
  have hxpow : ∃ k : ℕ, pairElem i₀ j₀ μ hμ ^ p ^ k = 1 := by
    obtain ⟨m, hm⟩ := hpμ
    refine ⟨m, ?_⟩
    have h2 : pairElem i₀ j₀ μ hμ =
        (TypeA.permSL σ)⁻¹ * pairElem a b μ hμ * ((TypeA.permSL σ)⁻¹)⁻¹ := by
      rw [← hconj]
      group
    rw [h2, conj_pow, hm]
    simp
  have hxblock : pairElem i₀ j₀ μ hμ ∈
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I :=
    pairElem_mem_blockSpecialLinear hi₀ hj₀ μ hμ
  have hxdiag : ∃ w : Fin d → K,
      ((pairElem i₀ j₀ μ hμ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal w :=
    ⟨_, coe_pairElem i₀ j₀ μ hμ⟩
  have hmem : TypeA.permSL σ * pairElem i₀ j₀ μ hμ * (TypeA.permSL σ)⁻¹ ∈
      permConjClosureSL (p := p) I :=
    Subgroup.subset_closure (Set.mem_iUnion.mpr
      ⟨σ, ⟨pairElem i₀ j₀ μ hμ, ⟨hxblock, hxdiag, hxpow⟩, rfl⟩⟩)
  rwa [hconj] at hmem

theorem diag_pElt_mem_closure_permConj_SL
    {d p : ℕ} {K : Type} [Field K] [CharP K 2]
    (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    (s : SpecialLinearGroup (Fin d) K)
    (hs : ∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v)
    (hsp : ∃ k : ℕ, s ^ p ^ k = 1) :
    s ∈ Subgroup.closure (⋃ σ : Equiv.Perm (Fin d),
      (fun x => TypeA.permSL σ * x * (TypeA.permSL σ)⁻¹) ''
        {x : SpecialLinearGroup (Fin d) K |
          x ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := K) I ∧
          (∃ v : Fin d → K, (x : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
          ∃ k : ℕ, x ^ p ^ k = 1}) := by
  classical
  change s ∈ permConjClosureSL (p := p) I
  obtain ⟨v, hv⟩ := hs
  obtain ⟨k, hk⟩ := hsp
  have hprod : ∏ i, v i = 1 := by
    have h1 := s.2
    rwa [hv, Matrix.det_diagonal] at h1
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i h0
    have h1 : (∏ i, v i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hprod] at h1
    exact one_ne_zero h1
  have hvpow : ∀ i, v i ^ p ^ k = 1 := by
    intro i
    have h1 : (diagonal v) ^ p ^ k = 1 := by
      have h2 := congrArg (fun x : SpecialLinearGroup (Fin d) K =>
        (x : Matrix (Fin d) (Fin d) K)) hk
      simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hv] using h2
    have h2 : diagonal (v ^ p ^ k) = 1 := by rwa [Matrix.diagonal_pow] at h1
    have h3 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) h2
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.pow_apply] using h3
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  have hFmem : ∀ k' : Fin d, pairElem k' i₀ (v k') (hv0 k') ∈ permConjClosureSL (p := p) I := by
    intro k'
    by_cases hk' : k' = i₀
    · subst hk'
      rw [pairElem_self]
      exact Subgroup.one_mem _
    · exact pairElem_mem_closure I hI hk' (v k') (hv0 k')
        ⟨k, pairElem_pow_eq_one k' i₀ (v k') (hv0 k') (hvpow k')⟩
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
    { carrier := {u | ∃ D : SpecialLinearGroup (Fin d) K,
        D ∈ permConjClosureSL (p := p) I ∧
        (D : Matrix (Fin d) (Fin d) K) = diagonal u}
      one_mem' := ⟨1, Subgroup.one_mem _,
        by rw [Matrix.SpecialLinearGroup.coe_one]; exact Matrix.diagonal_one.symm⟩
      mul_mem' := by
        rintro u w ⟨Du, hDu, hDu'⟩ ⟨Dw, hDw, hDw'⟩
        refine ⟨Du * Dw, Subgroup.mul_mem _ hDu hDw, ?_⟩
        rw [Matrix.SpecialLinearGroup.coe_mul, hDu', hDw', Matrix.diagonal_mul_diagonal]
        rfl }
  have hvM : v ∈ M := by
    have hmem : (∏ k', TypeA.ggPairVec k' i₀ (v k')) ∈ M :=
      M.prod_mem (fun k' _ =>
        ⟨pairElem k' i₀ (v k') (hv0 k'), hFmem k', coe_pairElem k' i₀ (v k') (hv0 k')⟩)
    rwa [hfun] at hmem
  obtain ⟨D, hD, hDv⟩ := hvM
  have hDs : D = s := by
    apply Subtype.ext
    rw [hDv, hv]
  rw [← hDs]
  exact hD

end CFSG.StandardType
