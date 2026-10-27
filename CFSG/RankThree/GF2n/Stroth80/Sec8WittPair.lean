module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating
open scoped Matrix

theorem exists_statedSp_mulVec_pair {m : ℕ} {K : Type} [Field K]
    {e f e' f' : Fin m ⊕ Fin m → K} (h : spForm m K e f = spForm m K e' f')
    (h0 : spForm m K e f ≠ 0) :
    ∃ A ∈ StatedSp m K, (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e = e' ∧
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ f = f' := by
  have hinv : (spForm m K e f)⁻¹ * spForm m K e f = 1 := inv_mul_cancel₀ h0
  have hf₀ : spForm m K e ((spForm m K e f)⁻¹ • f) = 1 := by
    rw [map_smul, smul_eq_mul, hinv]
  have hf₀' : spForm m K e' ((spForm m K e f)⁻¹ • f') = 1 := by
    rw [map_smul, smul_eq_mul, ← h, hinv]
  obtain ⟨g, hge, hgf⟩ := exists_gsp_pair spForm_isAlt spForm_nondegenerate hf₀ hf₀'
  have hAx : ∀ x : Fin m ⊕ Fin m → K,
      (((spEquiv (m := m) (K := K)).symm g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = g.app x := by
    intro x
    have hx := spEquiv_app ((spEquiv (m := m) (K := K)).symm g) x
    rw [MulEquiv.apply_symm_apply] at hx
    exact hx.symm
  refine ⟨((spEquiv (m := m) (K := K)).symm g : GL (Fin m ⊕ Fin m) K),
    ((spEquiv (m := m) (K := K)).symm g).2, (hAx e).trans hge, ?_⟩
  rw [← smul_inv_smul₀ h0 f, Matrix.mulVec_smul, hAx, hgf, smul_inv_smul₀ h0 f']

end CFSG.ClassicalGroups.Symplectic
