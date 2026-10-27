module

public import CFSG.LargeExtraspecial.O62Model

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

theorem s16c1G_vec_xor (x y : ℕ) : vec (x ^^^ y) = vec x + vec y := by
  funext i
  simp [vec, bitZ_xor]

theorem s16c1G_exists_vec (u : V₀) : ∃ n : ℕ, n < 64 ∧ vec n = u := by
  have h : ∀ u : V₀, ∃ n : Fin 64, vec (n : ℕ) = u := by decide +kernel
  obtain ⟨n, hn⟩ := h u
  exact ⟨n, n.isLt, hn⟩

theorem s16c1G_apply_vec {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ} (hg : HasCode (g : V₀ →ₗ[ZMod 2] V₀) m)
    (n : ℕ) : g (vec n) = vec (act m n) := by
  calc g (vec n) = (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀)).mulVec (vec n) :=
        (LinearMap.toMatrix'_mulVec _ _).symm
    _ = (mat m).mulVec (vec n) := by rw [hg]
    _ = vec (act m n) := (vec_act m n).symm

theorem s16c1G_qB_eq_false {a : ℕ} (h : qModel true (vec a) = 0) : qB true a = false := by
  rw [qModel_vec] at h
  by_contra hb
  have hb' : qB true a = true := by simpa using hb
  rw [if_pos hb'] at h
  exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
