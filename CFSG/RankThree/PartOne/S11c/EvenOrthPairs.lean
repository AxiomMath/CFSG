module

public import CFSG.RankThree.PartOne.S11c.EvenOrthBlocks

import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.HNRed

open Matrix

structure PairSys (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (Q : (ι → K) → K) (m : ℕ) where
  xs : Fin m → ι
  ys : Fin m → ι
  xs_inj : Function.Injective xs
  ys_inj : Function.Injective ys
  xs_ne_ys : ∀ i j, xs i ≠ ys j
  R : (ι → K) → K
  hR : ∀ v w : ι → K, (∀ a, (∀ i, a ≠ xs i ∧ a ≠ ys i) → w a = 0) → R (v + w) = R v
  hQ : ∀ v, Q v = ∑ i, v (xs i) * v (ys i) + R v

section Pairs

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K}
  {m : ℕ} (P : PairSys K ι Q m)

theorem PairSys.four_ne {p p' : Fin m} (h : p ≠ p') :
    P.xs p ≠ P.xs p' ∧ P.xs p ≠ P.ys p' ∧ P.ys p ≠ P.xs p' ∧ P.ys p ≠ P.ys p' :=
  ⟨fun e => h (P.xs_inj e), P.xs_ne_ys _ _, fun e => P.xs_ne_ys p' p e.symm,
    fun e => h (P.ys_inj e)⟩

@[expose] def PairSys.blockEmb {p p' : Fin m} (h : p ≠ p') : Fin 4 ↪ ι where
  toFun := ![P.xs p, P.ys p, P.xs p', P.ys p']
  inj' := by
    obtain ⟨h1, h2, h3, h4⟩ := P.four_ne h
    have h5 := P.xs_ne_ys p p
    have h6 := P.xs_ne_ys p' p'
    intro s t hst
    fin_cases s <;> fin_cases t <;> first | rfl | (exfalso; simp at hst; grind)

theorem PairSys.blockEmb_apply {p p' : Fin m} (h : p ≠ p') :
    ((P.blockEmb h : Fin 4 ↪ ι) : Fin 4 → ι) = ![P.xs p, P.ys p, P.xs p', P.ys p'] := rfl

theorem PairSys.incl_xs_p {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) :
    (incl K (P.blockEmb h) *ᵥ u) (P.xs p) = u 0 := by
  simpa [PairSys.blockEmb_apply] using incl_mulVec_emb (P.blockEmb h) u 0

theorem PairSys.incl_ys_p {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) :
    (incl K (P.blockEmb h) *ᵥ u) (P.ys p) = u 1 := by
  simpa [PairSys.blockEmb_apply] using incl_mulVec_emb (P.blockEmb h) u 1

theorem PairSys.incl_xs_p' {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) :
    (incl K (P.blockEmb h) *ᵥ u) (P.xs p') = u 2 := by
  simpa [PairSys.blockEmb_apply] using incl_mulVec_emb (P.blockEmb h) u 2

theorem PairSys.incl_ys_p' {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) :
    (incl K (P.blockEmb h) *ᵥ u) (P.ys p') = u 3 := by
  simpa [PairSys.blockEmb_apply] using incl_mulVec_emb (P.blockEmb h) u 3

theorem PairSys.incl_xs_of_ne {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) {i : Fin m}
    (hp : i ≠ p) (hp' : i ≠ p') : (incl K (P.blockEmb h) *ᵥ u) (P.xs i) = 0 := by
  apply incl_mulVec_of_ne
  intro s
  fin_cases s
  · exact fun e => hp (P.xs_inj e).symm
  · exact fun e => P.xs_ne_ys _ _ e.symm
  · exact fun e => hp' (P.xs_inj e).symm
  · exact fun e => P.xs_ne_ys _ _ e.symm

theorem PairSys.incl_ys_of_ne {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) {i : Fin m}
    (hp : i ≠ p) (hp' : i ≠ p') : (incl K (P.blockEmb h) *ᵥ u) (P.ys i) = 0 := by
  apply incl_mulVec_of_ne
  intro s
  fin_cases s
  · exact fun e => P.xs_ne_ys _ _ e
  · exact fun e => hp (P.ys_inj e).symm
  · exact fun e => P.xs_ne_ys _ _ e
  · exact fun e => hp' (P.ys_inj e).symm

theorem PairSys.incl_apply_other {p p' : Fin m} (h : p ≠ p') (u : Fin 4 → K) (a : ι)
    (ha : ∀ i, a ≠ P.xs i ∧ a ≠ P.ys i) : (incl K (P.blockEmb h) *ᵥ u) a = 0 := by
  apply incl_mulVec_of_ne
  intro s
  fin_cases s
  · exact fun e => (ha p).1 (by simpa [PairSys.blockEmb_apply] using e.symm)
  · exact fun e => (ha p).2 (by simpa [PairSys.blockEmb_apply] using e.symm)
  · exact fun e => (ha p').1 (by simpa [PairSys.blockEmb_apply] using e.symm)
  · exact fun e => (ha p').2 (by simpa [PairSys.blockEmb_apply] using e.symm)

theorem PairSys.Q_add_incl {p p' : Fin m} (h : p ≠ p') (v : ι → K) (u : Fin 4 → K) :
    Q (v + incl K (P.blockEmb h) *ᵥ u) = Q v + quad4 u +
      (v (P.xs p) * u 1 + v (P.ys p) * u 0 + v (P.xs p') * u 3 + v (P.ys p') * u 2) := by
  have hR : P.R (v + incl K (P.blockEmb h) *ᵥ u) = P.R v :=
    P.hR v _ (fun a ha => P.incl_apply_other h u a ha)
  rw [P.hQ, P.hQ, hR]
  have hsum : ∑ i, (v + incl K (P.blockEmb h) *ᵥ u) (P.xs i) *
        (v + incl K (P.blockEmb h) *ᵥ u) (P.ys i) - ∑ i, v (P.xs i) * v (P.ys i) =
      (v (P.xs p) * u 1 + u 0 * v (P.ys p) + u 0 * u 1) +
        (v (P.xs p') * u 3 + u 2 * v (P.ys p') + u 2 * u 3) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_add p p' h]
    · simp only [Pi.add_apply, P.incl_xs_p h, P.incl_ys_p h, P.incl_xs_p' h, P.incl_ys_p' h]
      ring
    · intro c _ hc
      simp only [Pi.add_apply, P.incl_xs_of_ne h u hc.1 hc.2, P.incl_ys_of_ne h u hc.1 hc.2]
      ring
    · intro hp
      exact absurd (Finset.mem_univ p) hp
    · intro hp
      exact absurd (Finset.mem_univ p') hp
  simp only [quad4]
  linear_combination hsum

theorem PairSys.blockGL_isometry {p p' : Fin m} (h : p ≠ p')
    (g : Matrix.GeneralLinearGroup (Fin 4) K)
    (hg : ∀ a : Fin 4 → K, quad4 ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ a) = quad4 a)
    (v : ι → K) :
    Q (((blockGL (P.blockEmb h) g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v) =
      Q v := by
  rw [blockGL_coe, blockExt_mulVec]
  set a : Fin 4 → K := (incl K (P.blockEmb h))ᵀ *ᵥ v with ha
  set u : Fin 4 → K := ((g : Matrix (Fin 4) (Fin 4) K) - 1) *ᵥ a with hu
  rw [P.Q_add_incl h v u]
  have hMa : (g : Matrix (Fin 4) (Fin 4) K) *ᵥ a = a + u := by
    rw [hu, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hq := hg a
  rw [hMa] at hq
  have hq' : quad4 (a + u) = quad4 a + quad4 u +
      (a 0 * u 1 + a 1 * u 0 + a 2 * u 3 + a 3 * u 2) := by
    simp only [quad4, Pi.add_apply]
    ring
  have ha0 : a 0 = v (P.xs p) := inclT_mulVec (P.blockEmb h) v 0
  have ha1 : a 1 = v (P.ys p) := inclT_mulVec (P.blockEmb h) v 1
  have ha2 : a 2 = v (P.xs p') := inclT_mulVec (P.blockEmb h) v 2
  have ha3 : a 3 = v (P.ys p') := inclT_mulVec (P.blockEmb h) v 3
  rw [← ha0, ← ha1, ← ha2, ← ha3]
  have := hq'.symm.trans hq
  linear_combination this

end Pairs

end CFSG.RankThree.PartOne.HNRed
