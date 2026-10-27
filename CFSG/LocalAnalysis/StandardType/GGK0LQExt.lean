module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus


@[expose] def lqExtRoot (τ : Tag) (T : GGKacType) (x : ℕ) : Fin τ.rank → ℤ :=
  fun j => if x = 0 then -(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)
    else if j.val + 1 = x then 1 else 0

private theorem lk0xlqroots_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private theorem lk0xlqroots_marks_pos (T : GGKacType) (i : Fin (k0DiagOf T).marks.length) :
    0 < (k0DiagOf T).marks.getD i.val 0 := by
  cases T <;> fin_cases i <;> decide

private theorem lk0xlqroots_lqExtRoot_zero' (T : GGKacType) (j : Fin (absTag T).rank) :
    ((lqExtRoot (absTag T) T 0 j : ℤ) : ℚ) =
      -(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℚ) := by
  unfold lqExtRoot
  rw [if_pos rfl]
  push_cast
  ring

private theorem lk0xlqroots_lqExtRoot_zero (T : GGKacType) (x : ℕ) (hx : x ≠ 0)
    (j : Fin (absTag T).rank) :
    ((lqExtRoot (absTag T) T x j : ℤ) : ℚ) = if j.val + 1 = x then 1 else 0 := by
  unfold lqExtRoot
  rw [if_neg hx]
  split_ifs with h
  · push_cast; ring
  · push_cast; ring

private theorem lk0xlqroots_elem_coord (T : GGKacType) (y : ℕ)
    (hy : y ≠ 0) (hy_lt : y < (k0DiagOf T).marks.length) :
    ∃ j : Fin (absTag T).rank, j.val + 1 = y := by
  have hlen := lk0xlqroots_marks_length T
  rw [hlen] at hy_lt
  refine ⟨⟨y - 1, by omega⟩, ?_⟩
  rw [Fin.val_mk]
  omega

private theorem lk0xlqroots_sum_isolate
    (T : GGKacType) (c : List ℕ)
    (g : {x // x ∈ c} → ℚ) (y : {x // x ∈ c}) (hy : y.1 ≠ 0)
    (j : Fin (absTag T).rank) (hj : j.val + 1 = y.1)
    (hz : ∀ (h0 : 0 ∈ c), g ⟨0, h0⟩ = 0) :
    (∑ x : {x // x ∈ c}, g x * ((lqExtRoot (absTag T) T x.1 j : ℤ) : ℚ)) = g y := by
  have h1 : (∑ x : {x // x ∈ c}, g x * ((lqExtRoot (absTag T) T x.1 j : ℤ) : ℚ))
      = g y * ((lqExtRoot (absTag T) T y.1 j : ℤ) : ℚ) := by
    refine Finset.sum_eq_single (a := y) ?_ ?_
    · intro b _ hb
      by_cases hb0 : b.1 = 0
      · have hgb : g b = 0 := by
          have hb_eq : b = (⟨0, hb0 ▸ b.2⟩ : {x // x ∈ c}) := Subtype.ext hb0
          rw [hb_eq, hz (hb0 ▸ b.2)]
        rw [hgb, zero_mul]
      · rw [lk0xlqroots_lqExtRoot_zero T b.1 hb0]
        have hne : j.val + 1 ≠ b.1 := by
          rw [hj]; intro h; exact hb (Subtype.ext h.symm)
        rw [if_neg hne, mul_zero]
    · intro hnot; exact absurd (Finset.mem_univ y) hnot
  rw [h1, lk0xlqroots_lqExtRoot_zero T y.1 hy, if_pos hj, mul_one]

theorem lq_extRoot_independent (τ : Tag) (T : GGKacType) (hτ : absTag T = τ) (c : List ℕ)
    (hnd : c.Nodup) (hc : ∀ x ∈ c, x < (k0DiagOf T).marks.length)
    (hproper : ∃ i < (k0DiagOf T).marks.length, i ∉ c) :
    LinearIndependent ℚ
      (fun x : {x // x ∈ c} => (fun j : Fin τ.rank => ((lqExtRoot τ T x.1 j : ℤ) : ℚ))) := by
  subst τ
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcoord : ∀ j : Fin (absTag T).rank,
      (∑ x : {x // x ∈ c}, g x * ((lqExtRoot (absTag T) T x.1 j : ℤ) : ℚ)) = 0 := by
    intro j
    have h := congrFun hg j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  intro y
  by_cases h0c : 0 ∈ c
  · obtain ⟨i, hi_lt, hi_notin⟩ := hproper
    have hi0 : i ≠ 0 := fun h => hi_notin (h ▸ h0c)
    obtain ⟨j, hj⟩ := lk0xlqroots_elem_coord T i hi0 hi_lt
    have hsingle : (∑ x : {x // x ∈ c},
        g x * ((lqExtRoot (absTag T) T x.1 j : ℤ) : ℚ)) =
        g ⟨0, h0c⟩ * (-(((k0DiagOf T).marks.getD i 0 : ℕ) : ℚ)) := by
      have h1 : (∑ x : {x // x ∈ c},
          g x * ((lqExtRoot (absTag T) T x.1 j : ℤ) : ℚ))
          = g ⟨0, h0c⟩ * ((lqExtRoot (absTag T) T 0 j : ℤ) : ℚ) := by
        refine Finset.sum_eq_single (a := (⟨0, h0c⟩ : {x // x ∈ c})) ?_ ?_
        · intro b _ hb
          have hb0 : b.1 ≠ 0 := fun h => hb (Subtype.ext h)
          rw [lk0xlqroots_lqExtRoot_zero T b.1 hb0]
          have hne : j.val + 1 ≠ b.1 := by
            rw [hj]; intro h; exact hi_notin (h ▸ b.2)
          rw [if_neg hne, mul_zero]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      rw [h1]
      have hv : ((lqExtRoot (absTag T) T (⟨0, h0c⟩ : {x // x ∈ c}).1 j : ℤ) : ℚ)
          = -(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℚ) := by
        simpa using lk0xlqroots_lqExtRoot_zero' T j
      rw [hv, hj]
    have hz := hcoord j
    rw [hsingle] at hz
    have hm : (((k0DiagOf T).marks.getD i 0 : ℕ) : ℚ) ≠ 0 := by
      have hpos := lk0xlqroots_marks_pos T ⟨i, hi_lt⟩
      exact_mod_cast ne_of_gt hpos
    have hz0 : g ⟨0, h0c⟩ = 0 := (mul_eq_zero.mp hz).resolve_right (neg_ne_zero.mpr hm)
    have hz' : ∀ (h0 : 0 ∈ c), g ⟨0, h0⟩ = 0 := by
      intro h0
      rw [show (⟨0, h0⟩ : {x // x ∈ c}) = ⟨0, h0c⟩ from Subtype.ext rfl]
      exact hz0
    by_cases hy0 : y.1 = 0
    · rw [show y = ⟨0, h0c⟩ from Subtype.ext hy0]; exact hz0
    · obtain ⟨j', hj'⟩ := lk0xlqroots_elem_coord T y.1 hy0 (hc y.1 y.2)
      have h := hcoord j'
      rw [lk0xlqroots_sum_isolate T c g y hy0 j' hj' hz'] at h
      exact h
  · have hz' : ∀ (h0 : 0 ∈ c), g ⟨0, h0⟩ = 0 := fun h0 => absurd h0 h0c
    have hy0 : y.1 ≠ 0 := fun h => h0c (h ▸ y.2)
    obtain ⟨j, hj⟩ := lk0xlqroots_elem_coord T y.1 hy0 (hc y.1 y.2)
    have h := hcoord j
    rw [lk0xlqroots_sum_isolate T c g y hy0 j hj hz'] at h
    exact h

end CFSG.StandardType.GGK0LQ

end
