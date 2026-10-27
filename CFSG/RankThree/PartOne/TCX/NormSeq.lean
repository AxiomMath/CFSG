module

public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.TCX

section Iterate

variable {G : Type*} [Group G]

@[expose] def nseq (n₀ : G) (F₀ : G →* G) : ℕ → G
  | 0 => 1
  | k + 1 => n₀ * F₀ (nseq n₀ F₀ k)

theorem nseq_zero (n₀ : G) (F₀ : G →* G) : nseq n₀ F₀ 0 = 1 := rfl

theorem nseq_succ (n₀ : G) (F₀ : G →* G) (k : ℕ) :
    nseq n₀ F₀ (k + 1) = n₀ * F₀ (nseq n₀ F₀ k) := rfl

theorem iterate_lang_nseq {F₀ : G →* G} {g₀ n₀ : G} (hg : F₀ g₀ = g₀ * n₀) (k : ℕ) :
    (⇑F₀)^[k] g₀ = g₀ * nseq n₀ F₀ k := by
  induction k with
  | zero => simp [nseq]
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, hg, nseq, mul_assoc]

theorem iterate_conj_nseq (F₀ : G →* G) (n₀ : G) (k : ℕ) (w : G) :
    (fun v => n₀ * F₀ v * n₀⁻¹)^[k] w =
      nseq n₀ F₀ k * (⇑F₀)^[k] w * (nseq n₀ F₀ k)⁻¹ := by
  induction k generalizing w with
  | zero => simp [nseq, inv_one, mul_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_mul,
      map_inv, nseq]
    group

theorem nseq_conj_fixed {F₀ : G →* G} {n₀ u : G} (hu : n₀ * F₀ u * n₀⁻¹ = u) (k : ℕ) :
    nseq n₀ F₀ k * (⇑F₀)^[k] u * (nseq n₀ F₀ k)⁻¹ = u := by
  rw [← iterate_conj_nseq]
  exact Function.iterate_fixed hu k

theorem nseq_eq_pow {F₀ : G →* G} {n₀ : G} (hn : F₀ n₀ = n₀) (k : ℕ) :
    nseq n₀ F₀ k = n₀ ^ k := by
  induction k with
  | zero => simp [nseq]
  | succ k ih => rw [nseq_succ, ih, map_pow, hn, pow_succ']

end Iterate

end CFSG.RankThree.PartOne.TCX
