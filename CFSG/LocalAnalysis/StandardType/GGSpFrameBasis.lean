module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameRefl
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

public section

namespace CFSG.StandardType.SpFrame

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_downward_family {m : ℕ} (T : Fin (m + 1) → Module.End k V) (b : V) :
    ∃ f : Fin (m + 1) → V, f (Fin.last m) = b ∧
      ∀ (i : Fin (m + 1)) (hi : i.val + 1 < m + 1), f i = T i (f ⟨i.val + 1, hi⟩) := by
  let T' : ℕ → Module.End k V := fun t => if h : t < m + 1 then T ⟨t, h⟩ else 0
  let g : ℕ → V := fun t => Nat.rec b (fun s ih => T' (m - (s + 1)) ih) t
  have g_succ : ∀ s : ℕ, g (s + 1) = T' (m - (s + 1)) (g s) := by
    intro s
    simp only [g]
  have hT' : ∀ (i : Fin (m + 1)), T' i.val = T i := by
    intro i
    simp only [T', dif_pos i.isLt]
  refine ⟨fun i => g (m - i.val), ?_, ?_⟩
  · show g (m - (Fin.last m).val) = b
    rw [show (Fin.last m).val = m from rfl, Nat.sub_self]
    rfl
  · intro i hi
    change g (m - i.val) = T i (g (m - (i.val + 1)))
    have hsplit : m - i.val = (m - (i.val + 1)) + 1 := by omega
    rw [hsplit, g_succ]
    have hsub : m - ((m - (i.val + 1)) + 1) = i.val := by omega
    rw [hsub, hT' i]

theorem isRefl_of_sign_family {m : ℕ} (T ε : Fin (m + 1) → Module.End k V)
    (hT : ∀ (i : Fin (m + 1)), i.val + 1 < m + 1 → IsRefl (T i))
    (hεlast : IsRefl (ε (Fin.last m)))
    (hconj : ∀ (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) (j : Fin (m + 1)),
      T i * ε j * T i = ε (Equiv.swap i ⟨i.val + 1, hi⟩ j)) (j : Fin (m + 1)) : IsRefl (ε j) := by
  have key : ∀ t : ℕ, ∀ j : Fin (m + 1), m - j.val = t → IsRefl (ε j) := by
    intro t
    induction t with
    | zero =>
      intro j hj
      have hjval : j.val = m := by
        have hle : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
        omega
      have hlast : j = Fin.last m := by
        ext
        simpa [Fin.val_last] using hjval
      rw [hlast]
      exact hεlast
    | succ t ih =>
      intro j hj
      have hle : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
      have hjlt : j.val < m := by omega
      have hi : j.val + 1 < m + 1 := by omega
      let j' : Fin (m + 1) := ⟨j.val + 1, hi⟩
      have hj't : m - j'.val = t := by
        simp only [j', Fin.val_mk]
        omega
      have hrefl' : IsRefl (ε j') := ih j' hj't
      have hconjj : T j * ε j' * T j = ε j := by
        rw [hconj j hi j', Equiv.swap_apply_right]
      rw [← hconjj]
      exact IsRefl.conj hrefl' (hT j hi).1 (hT j hi).1
  exact key (m - j.val) j rfl

end CFSG.StandardType.SpFrame
