module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def foldVert (ℓ : Line Γ) (a : ℤ) (m : ℕ) (x : G) (k : ℕ) : V :=
  if k ≤ m then ℓ.vert (a + k) else x • ℓ.vert (a + 2 * (m : ℤ) - k)

theorem foldVert_le (ℓ : Line Γ) (a : ℤ) (m : ℕ) (x : G) {k : ℕ} (hk : k ≤ m) :
    foldVert ℓ a m x k = ℓ.vert (a + k) := by
  simp [foldVert, hk]

theorem foldVert_ge (ℓ : Line Γ) (a : ℤ) (m : ℕ) (x : G)
    (hfix : x • ℓ.vert (a + m) = ℓ.vert (a + m)) {k : ℕ} (hk : m ≤ k) :
    foldVert ℓ a m x k = x • ℓ.vert (a + 2 * (m : ℤ) - k) := by
  by_cases h : k ≤ m
  · have hkm : k = m := le_antisymm h hk
    subst hkm
    rw [foldVert_le ℓ a k x le_rfl, show a + 2 * (k : ℤ) - k = a + k by ring, hfix]
  · simp [foldVert, h]

@[expose] def foldArc (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (ℓ : Line Γ) (a : ℤ) (m : ℕ) (x : G) (hfix : x • ℓ.vert (a + m) = ℓ.vert (a + m))
    (hmove : x • ℓ.vert (a + m - 1) ≠ ℓ.vert (a + m - 1)) : Arc Γ (2 * m) where
  vert := foldVert ℓ a m x
  adj k hk := by
    by_cases h1 : k + 1 ≤ m
    · rw [foldVert_le ℓ a m x (by omega), foldVert_le ℓ a m x h1,
        show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
      exact ℓ.adj _
    · rw [foldVert_ge ℓ a m x hfix (by omega), foldVert_ge ℓ a m x hfix (by omega),
        show a + 2 * (m : ℤ) - ((k + 1 : ℕ) : ℤ) = a + 2 * (m : ℤ) - k - 1 by push_cast; ring]
      exact (hadj x _ _).2 (ℓ.adj_pred _)
  nb k hk := by
    by_cases h1 : k + 2 ≤ m
    · rw [foldVert_le ℓ a m x (by omega), foldVert_le ℓ a m x h1,
        show a + ((k + 2 : ℕ) : ℤ) = a + k + 2 by push_cast; ring]
      exact ℓ.nb _
    · by_cases h2 : k + 1 = m
      · rw [foldVert_le ℓ a m x (by omega), foldVert_ge ℓ a m x hfix (by omega),
          show a + (k : ℤ) = a + m - 1 by omega,
          show a + 2 * (m : ℤ) - ((k + 2 : ℕ) : ℤ) = a + m - 1 by push_cast; omega]
        exact fun h => hmove h.symm
      · rw [foldVert_ge ℓ a m x hfix (by omega), foldVert_ge ℓ a m x hfix (by omega),
          show a + 2 * (m : ℤ) - ((k + 2 : ℕ) : ℤ) = a + 2 * (m : ℤ) - k - 2 by push_cast; ring]
        have := ℓ.nb (a + 2 * (m : ℤ) - k - 2)
        rw [show a + 2 * (m : ℤ) - k - 2 + 2 = a + 2 * (m : ℤ) - k by ring] at this
        exact fun h => this (MulAction.injective x h).symm

end CFSG.Quasithin.Fan86
