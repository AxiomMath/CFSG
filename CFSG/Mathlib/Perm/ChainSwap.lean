module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.Fin.Basic

public section

namespace CFSG.Perm

theorem swap_mem_closure_chainSwap {α : Type*} [DecidableEq α] {m : ℕ} {c : Fin (m + 1) → α}
    (hc : Function.Injective c) (i j : Fin (m + 1)) :
    Equiv.swap (c i) (c j) ∈
      Subgroup.closure (Set.range fun κ : Fin m => Equiv.swap (c κ.castSucc) (c κ.succ)) := by
  have key : ∀ (a n : ℕ) (h : a + n < m + 1), Equiv.swap (c ⟨a, by omega⟩) (c ⟨a + n, h⟩) ∈
      Subgroup.closure (Set.range fun κ : Fin m => Equiv.swap (c κ.castSucc) (c κ.succ)) := by
    intro a n
    induction n with
    | zero =>
      intro h
      have h1 : Equiv.swap (c ⟨a, by omega⟩) (c ⟨a + 0, h⟩) = 1 := Equiv.swap_self _
      rw [h1]
      exact Subgroup.one_mem _
    | succ n ih =>
      intro h
      have h2 : Equiv.swap (c ⟨a + n, by omega⟩) (c ⟨a + (n + 1), h⟩) ∈
          Subgroup.closure (Set.range fun κ : Fin m => Equiv.swap (c κ.castSucc) (c κ.succ)) :=
        Subgroup.subset_closure ⟨⟨a + n, by omega⟩, rfl⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact h2
      · have hxy : c ⟨a, by omega⟩ ≠ c ⟨a + n, by omega⟩ :=
          hc.ne (by rw [Ne, Fin.ext_iff]; simp only; omega)
        have hxz : c ⟨a, by omega⟩ ≠ c ⟨a + (n + 1), h⟩ :=
          hc.ne (by rw [Ne, Fin.ext_iff]; simp only; omega)
        rw [Equiv.swap_comm, ← Equiv.swap_mul_swap_mul_swap hxy hxz]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 (ih (by omega))) h2
  rcases le_total i j with hij | hij
  · have := key i (j - i) (by omega)
    have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin (m + 1)) = j := Fin.ext (by simp only; omega)
    rwa [hj] at this
  · have := key j (i - j) (by omega)
    have hi : (⟨(j : ℕ) + (i - j), by omega⟩ : Fin (m + 1)) = i := Fin.ext (by simp only; omega)
    rw [hi] at this
    rwa [Equiv.swap_comm]

theorem map_swap_mem_closure_chainSwap {α G : Type*} [DecidableEq α] [Group G]
    (φ : Equiv.Perm α →* G) {m : ℕ} {c : Fin (m + 1) → α} (hc : Function.Injective c)
    (i j : Fin (m + 1)) :
    φ (Equiv.swap (c i) (c j)) ∈
      Subgroup.closure (Set.range fun κ : Fin m => φ (Equiv.swap (c κ.castSucc) (c κ.succ))) := by
  have h : Set.range (fun κ : Fin m => φ (Equiv.swap (c κ.castSucc) (c κ.succ))) =
      φ '' Set.range fun κ : Fin m => Equiv.swap (c κ.castSucc) (c κ.succ) := by
    rw [← Set.range_comp]
    rfl
  rw [h, ← MonoidHom.map_closure]
  exact Subgroup.mem_map_of_mem φ (swap_mem_closure_chainSwap hc i j)

end CFSG.Perm

end
