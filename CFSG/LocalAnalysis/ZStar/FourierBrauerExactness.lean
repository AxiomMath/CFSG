module

public import CFSG.LocalAnalysis.ZStar.PadicTrace

public section

namespace CFSG

namespace ZStar.FourierBrauerExactness

noncomputable section

universe u

theorem modular_exact_of_nontrivial_eigenvalue
    {k : Type u} [Field k]
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q E : Matrix n n k) (zeta : k) (hzeta : zeta ≠ 1)
    (hquotient :
      ∀ x : n → k,
        x ∈ (Matrix.toLin' (P - 1)).ker →
          (Matrix.toLin' (Q - 1)) x ∈
            (Matrix.toLin' (P - 1)).range)
    (heigen :
      ∀ y : n → k,
        (Matrix.toLin' Q) ((Matrix.toLin' E) y) =
          zeta • (Matrix.toLin' E) y) :
    (Matrix.toLin' (P - 1)).ker ⊓
        (Matrix.toLin' E).range ≤
      (Matrix.toLin' (P - 1)).range := by
  intro x hx
  have hxker : x ∈ (Matrix.toLin' (P - 1)).ker := hx.1
  obtain ⟨y, hy⟩ := hx.2
  have hdiff :
      (Matrix.toLin' (Q - 1)) x = (zeta - 1) • x := by
    subst x
    rw [map_sub, Matrix.toLin'_one]
    change (Matrix.toLin' Q) ((Matrix.toLin' E) y) -
      (Matrix.toLin' E) y = _
    rw [heigen]
    simpa only [one_smul] using
      (sub_smul zeta 1 ((Matrix.toLin' E) y)).symm
  have hmem := hquotient x hxker
  rw [hdiff] at hmem
  have hscaled := (Matrix.toLin' (P - 1)).range.smul_mem
    (zeta - 1)⁻¹ hmem
  have hzetasub : zeta - 1 ≠ 0 := sub_ne_zero.mpr hzeta
  simpa only [smul_smul, inv_mul_cancel₀ hzetasub, one_smul] using hscaled

end

end ZStar.FourierBrauerExactness

end CFSG
