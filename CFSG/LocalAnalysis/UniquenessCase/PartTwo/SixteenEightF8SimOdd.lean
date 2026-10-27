module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.OddOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Open

private theorem s16g_mem_statedOmega_of_odd {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q))
    {g : GL ι K} (hg : ∀ v, Q₀ ((g : Matrix ι ι K) *ᵥ v) = Q₀ v) {k : ℕ} (hk : Odd k)
    (hgk : g ^ k = 1) : g ∈ StatedOmega Q₀ := by
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap]
  have hgO : (toLinEquiv ι K).toMonoidHom g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ]
      exact hg v
  refine mem_of_odd_pow_of_sq_mem (N := ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆) (fun x hx => ?_) hk (by rw [← map_pow, hgk, map_one])
  subst hx
  exact sq_mem_commutator_of_le_closure _ (Set.range (reflect Q))
    (by rintro _ ⟨v, rfl⟩; exact reflect_mem_orthogonalGroup _ v)
    (by rintro _ ⟨v, rfl⟩; rw [pow_two]; exact reflect_mul_self _ v) (by rw [hE]; exact hgen) hgO

theorem s16g_le_statedOmegaPlus_of_odd {K : Type} [Field K] [CharP K 2] {m : ℕ} (hm : 3 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hE : ∀ x ∈ E, x ^ p = 1)
    (hEQ : ∀ x ∈ E, ∀ v : Fin m ⊕ Fin m → K,
      StatedQuadPlus m K ((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
        StatedQuadPlus m K v) :
    E ≤ StatedOmega (StatedQuadPlus m K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hn0 : 0 < m := by omega
  intro x hx
  exact s16g_mem_statedOmega_of_odd (coe_quadPlus m K) (commutator_orthogonalGroup_quadPlus hm)
    (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0)
      (nondegenerate_polarBilin_quadPlus m K) h2
      (fun y hy _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hy)
      (fun y hy hy0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hy) hy0) (by omega))
    (hEQ x hx) (hp.odd_of_ne_two hp2) (hE x hx)

theorem s16g_le_statedOmegaMinus_of_odd {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hE : ∀ x ∈ E, x ^ p = 1)
    (hEQ : ∀ x ∈ E, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c ((x : Matrix _ _ K) *ᵥ v) = StatedQuadMinus m K b c v) :
    E ≤ StatedOmega (StatedQuadMinus m K b c) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hn0 : 0 < m - 1 := by omega
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  intro x hx
  exact s16g_mem_statedOmega_of_odd (coe_quadMinus m K b c)
    (commutator_orthogonalGroup_quadMinus_of_two_le hm hirr)
    (orthogonalGroup_le_closure_of_two_eq_zero (minusFamily_orth hn0) hnd h2
      (fun y hy hQ => eq_zero_of_mem_tailSpace_minusFamily hirr hn0 hy hQ)
      (fun y hy hy0 z hz hyz => exists_eq_smul_of_mem_tailSpace_minusFamily h2 hirr hn0 hy hy0 hz
        hyz) (by omega))
    (hEQ x hx) (hp.odd_of_ne_two hp2) (hE x hx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
