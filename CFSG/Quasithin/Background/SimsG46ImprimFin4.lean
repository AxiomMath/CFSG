module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

structure IsFpfInv (ε : Fin 4 → Fin 4) : Prop where
  invol : ∀ t, ε (ε t) = t
  ne : ∀ t, ε t ≠ t

private def kleinTbl : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

private theorem kleinTbl_classify : ∀ a b c d : Fin 4,
    (∀ x : Fin 4, ![a, b, c, d] (![a, b, c, d] x) = x) → (∀ x, ![a, b, c, d] x ≠ x) →
      ∀ t, ![a, b, c, d] t = kleinTbl a t := by
  decide

private theorem kleinTbl_comm : ∀ a b t : Fin 4,
    kleinTbl a (kleinTbl b t) = kleinTbl b (kleinTbl a t) := by
  decide

private theorem kleinTbl_swap : ∀ x y : Fin 4, x ≠ y →
    (∀ t, kleinTbl (kleinTbl x y) (kleinTbl (kleinTbl x y) t) = t) ∧
      (∀ t, kleinTbl (kleinTbl x y) t ≠ t) ∧ kleinTbl (kleinTbl x y) x = y := by
  decide

private theorem IsFpfInv.eq_kleinTbl {ε : Fin 4 → Fin 4} (hε : IsFpfInv ε) (t : Fin 4) :
    ε t = kleinTbl (ε 0) t := by
  have key := kleinTbl_classify (ε 0) (ε 1) (ε 2) (ε 3)
  have hvec : ![ε 0, ε 1, ε 2, ε 3] = ε := by
    funext x
    fin_cases x <;> rfl
  rw [hvec] at key
  exact key hε.invol hε.ne t

theorem IsFpfInv.comm {ε ε' : Fin 4 → Fin 4} (hε : IsFpfInv ε) (hε' : IsFpfInv ε') (t : Fin 4) :
    ε (ε' t) = ε' (ε t) := by
  rw [hε.eq_kleinTbl (ε' t), hε'.eq_kleinTbl t, hε'.eq_kleinTbl (ε t), hε.eq_kleinTbl t,
    kleinTbl_comm]

theorem exists_isFpfInv_apply_eq {x y : Fin 4} (hxy : x ≠ y) :
    ∃ ε : Fin 4 → Fin 4, IsFpfInv ε ∧ ε x = y := by
  obtain ⟨h1, h2, h3⟩ := kleinTbl_swap x y hxy
  exact ⟨kleinTbl (kleinTbl x y), ⟨h1, h2⟩, h3⟩

theorem IsFpfInv.conj {ε π ρ : Fin 4 → Fin 4} (hε : IsFpfInv ε) (hπρ : ∀ t, π (ρ t) = t)
    (hρπ : ∀ t, ρ (π t) = t) : IsFpfInv fun t => π (ε (ρ t)) := by
  refine ⟨fun t => ?_, fun t ht => ?_⟩
  · simp only [hρπ, hε.invol, hπρ]
  · apply hε.ne (ρ t)
    have h := congrArg ρ ht
    rwa [hρπ] at h

theorem eq_of_four {p q r s : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) (x : Fin 4) : x = p ∨ x = q ∨ x = r ∨ x = s := by
  revert p q r s x
  decide

theorem exists_ne_three (i j k : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  revert i j k
  decide

theorem exists_compl_pair {p q : Fin 4} (hpq : p ≠ q) :
    ∃ r s : Fin 4, r ≠ s ∧ r ≠ p ∧ r ≠ q ∧ s ≠ p ∧ s ≠ q := by
  revert p q
  decide

theorem false_of_three_in_pair {r s x y z : Fin 4} (hx : x = r ∨ x = s) (hy : y = r ∨ y = s)
    (hz : z = r ∨ z = s) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

theorem isFpfInv_comp_of_transp {π₁ π₂ : Fin 4 → Fin 4} {p q r s : Fin 4} (hpq : p ≠ q)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h1p : π₁ p = q) (h1q : π₁ q = p) (h1 : ∀ t, t ≠ p → t ≠ q → π₁ t = t)
    (h2r : π₂ r = s) (h2s : π₂ s = r) (h2 : ∀ t, t ≠ r → t ≠ s → π₂ t = t) :
    IsFpfInv fun t => π₁ (π₂ t) := by
  have e2p : π₂ p = p := h2 p hpr hps
  have e2q : π₂ q = q := h2 q hqr hqs
  have e1r : π₁ r = r := h1 r hpr.symm hqr.symm
  have e1s : π₁ s = s := h1 s hps.symm hqs.symm
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rcases eq_of_four hpq hpr hps hqr hqs hrs t with rfl | rfl | rfl | rfl <;>
      simp only [e2p, e2q, e1r, e1s, h1p, h1q, h2r, h2s]
  · rcases eq_of_four hpq hpr hps hqr hqs hrs t with rfl | rfl | rfl | rfl <;>
      simp only [e2p, e2q, e1r, e1s, h1p, h1q, h2r, h2s] <;>
      first | assumption | exact Ne.symm (by assumption)

theorem sq_eq_of_comm_isFpfInv {π : Fin 4 → Fin 4}
    (h : ∀ ε : Fin 4 → Fin 4, IsFpfInv ε → ∀ t, π (ε t) = ε (π t)) (t : Fin 4) :
    π (π t) = t := by
  by_cases ht : π t = t
  · rw [ht, ht]
  · obtain ⟨ε, hε, hεt⟩ := exists_isFpfInv_apply_eq (Ne.symm ht)
    calc π (π t) = π (ε t) := by rw [hεt]
      _ = ε (π t) := h ε hε t
      _ = ε (ε t) := by rw [hεt]
      _ = t := hε.invol t

end G46Imprim

end CFSG.Quasithin.SimsG4
