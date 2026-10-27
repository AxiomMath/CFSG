module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
open scoped Matrix

theorem spVec_add_self {m : ℕ} {K : Type} [Field K] [CharP K 2] (v : Fin m ⊕ Fin m → K) :
    v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem exists_transvection_LspGL_smul {m : ℕ} {K : Type} [Field K] (v : Fin m ⊕ Fin m → K)
    (c : K) :
    ∃ A ∈ LspGL m K v, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x + (c * spForm m K x v) • v := by
  set g := Tsp (spForm_isAlt (m := m) (K := K)) v c with hg
  set A : StatedSp m K := (spEquiv (m := m) (K := K)).symm g with hA
  refine ⟨(A : GL (Fin m ⊕ Fin m) K), mem_LspGL_iff.mpr ⟨A.2, ?_⟩, fun x => ?_⟩
  · have : spEquiv (m := m) (K := K) ⟨(A : GL (Fin m ⊕ Fin m) K), A.2⟩ = g := by
      show spEquiv (m := m) (K := K) A = g
      rw [hA, MulEquiv.apply_symm_apply]
    rw [this]
    exact Tsp_mem_Lsp _ _ _
  · have h1 := spEquiv_app A x
    rw [hA, MulEquiv.apply_symm_apply, hg, Tsp_app] at h1
    rw [← h1]

theorem mulVec_cube_eq_self {m : ℕ} {K : Type} [Field K] [CharP K 2]
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) {u u' : Fin m ⊕ Fin m → K} {c s : K}
    (hcs : c * s * s = 1) (hu : M *ᵥ u = (c * s) • u') (hu' : M *ᵥ u' = u' + s • u)
    (hx : ∀ x, ∃ l r : K, M *ᵥ x = x + l • u + r • u') (x : Fin m ⊕ Fin m → K) :
    M *ᵥ (M *ᵥ (M *ᵥ x)) = x := by
  have hlin : ∀ (p q : K) (y z : Fin m ⊕ Fin m → K),
      M *ᵥ (p • y + q • z) = p • M *ᵥ y + q • M *ᵥ z := fun p q y z => by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hs1 : s * (c * s) = 1 := by
    rw [show s * (c * s) = c * s * s by ring]
    exact hcs
  have hMu : M *ᵥ (M *ᵥ u) = (c * s) • u' + u := by
    rw [hu, Matrix.mulVec_smul, hu', smul_add, smul_smul, hcs, one_smul]
  have hMu' : M *ᵥ (M *ᵥ u') = u' + s • u + u' := by
    rw [hu', Matrix.mulVec_add, Matrix.mulVec_smul, hu, hu', smul_smul, hs1, one_smul]
  have hu0 : u + M *ᵥ u + M *ᵥ (M *ᵥ u) = 0 := by
    rw [hMu, hu, show u + (c * s) • u' + ((c * s) • u' + u) =
      (u + u) + ((c * s) • u' + (c * s) • u') by abel]
    simp only [spVec_add_self, add_zero]
  have hu'0 : u' + M *ᵥ u' + M *ᵥ (M *ᵥ u') = 0 := by
    rw [hMu', hu', show u' + (u' + s • u) + (u' + s • u + u') =
      (u' + u') + (u' + u') + (s • u + s • u) by abel]
    simp only [spVec_add_self, add_zero]
  have hPn : ∀ l r : K, (l • u + r • u') + M *ᵥ (l • u + r • u') +
      M *ᵥ (M *ᵥ (l • u + r • u')) = 0 := by
    intro l r
    rw [hlin l r u u', hlin l r (M *ᵥ u) (M *ᵥ u')]
    have e : (l • u + r • u') + (l • M *ᵥ u + r • M *ᵥ u') +
        (l • M *ᵥ (M *ᵥ u) + r • M *ᵥ (M *ᵥ u')) =
        l • (u + M *ᵥ u + M *ᵥ (M *ᵥ u)) + r • (u' + M *ᵥ u' + M *ᵥ (M *ᵥ u')) := by
      simp only [smul_add]
      abel
    rw [e]
    simp only [hu0, hu'0, smul_zero, add_zero]
  obtain ⟨l, r, hxl⟩ := hx x
  have key : ∀ n : Fin m ⊕ Fin m → K, M *ᵥ x = x + n → n + M *ᵥ n + M *ᵥ (M *ᵥ n) = 0 →
      M *ᵥ (M *ᵥ (M *ᵥ x)) = x := by
    intro n hn hP
    have h2 : M *ᵥ (M *ᵥ x) = x + n + M *ᵥ n := by
      rw [hn, Matrix.mulVec_add, hn]
    have h3 : M *ᵥ (M *ᵥ (M *ᵥ x)) = x + n + M *ᵥ n + M *ᵥ (M *ᵥ n) := by
      rw [h2, Matrix.mulVec_add, Matrix.mulVec_add, hn]
    rw [h3, show x + n + M *ᵥ n + M *ᵥ (M *ᵥ n) = x + (n + M *ᵥ n + M *ᵥ (M *ᵥ n)) by abel,
      hP, add_zero]
  exact key (l • u + r • u') (by rw [hxl, add_assoc]) (hPn l r)

theorem exists_transvection_pair_order_three {m : ℕ} {K : Type} [Field K] [CharP K 2]
    {u u' : Fin m ⊕ Fin m → K} (huu' : spForm m K u u' ≠ 0) :
    ∃ a ∈ LspGL m K u, ∃ b ∈ LspGL m K u',
      (∃ y : Fin m ⊕ Fin m → K,
        spForm m K y ((a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0) ∧
      (∃ y : Fin m ⊕ Fin m → K,
        spForm m K y ((b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0) ∧
      (a * b) ^ 3 = 1 := by
  obtain ⟨a, ha, hax⟩ := exists_transvection_LspGL_smul u 1
  obtain ⟨c, hc⟩ : ∃ c : K, c * spForm m K u u' * spForm m K u u' = 1 :=
    ⟨(spForm m K u u' * spForm m K u u')⁻¹, by
      rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero huu' huu')]⟩
  obtain ⟨b, hb, hbx⟩ := exists_transvection_LspGL_smul u' c
  have hsym : spForm m K u' u = spForm m K u u' := by
    rw [← (spForm_isAlt (m := m) (K := K)).neg_eq, CharTwo.neg_eq]
  have hG : ∀ x : Fin m ⊕ Fin m → K,
      ((a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ x =
        x + (spForm m K x u + c * spForm m K x u' * spForm m K u' u) • u +
          (c * spForm m K x u') • u' := by
    intro x
    rw [← Matrix.mulVec_mulVec, hbx x, Matrix.mulVec_add, Matrix.mulVec_smul, hax x, hax u']
    simp only [one_mul, smul_add, smul_smul, add_smul]
    abel
  have hu : ((a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ u = (c * spForm m K u u') • u' := by
    rw [hG u, spForm_self, zero_add, hsym, hc, one_smul, spVec_add_self u, zero_add]
  have hu' : ((a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ u' = u' + spForm m K u u' • u := by
    simp only [hG u', spForm_self, mul_zero, zero_mul, add_zero, zero_smul, hsym]
  have hx : ∀ x : Fin m ⊕ Fin m → K, ∃ l r : K,
      ((a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ x = x + l • u + r • u' :=
    fun x => ⟨_, _, hG x⟩
  have hcube := mulVec_cube_eq_self ((a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
    (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hc hu hu' hx
  refine ⟨a, ha, b, hb, ⟨u', ?_⟩, ⟨u, ?_⟩, ?_⟩
  · rw [hax, map_add, map_smul, spForm_self, zero_add, smul_eq_mul, one_mul, hsym]
    exact mul_ne_zero huu' huu'
  · rw [hbx, map_add, map_smul, spForm_self, zero_add, smul_eq_mul, hc]
    exact one_ne_zero
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
    refine Matrix.ext_iff_mulVec.mpr fun x => ?_
    rw [Matrix.one_mulVec, pow_three', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hcube x

end CFSG.RankThree.GF2n.Stroth80
