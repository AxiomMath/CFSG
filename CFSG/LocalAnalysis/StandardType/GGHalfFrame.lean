module

public import CFSG.LocalAnalysis.StandardType.GGHalfFrameGF2
public import CFSG.LocalAnalysis.StandardType.GGHalfFramePerm

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem exists_conj_into_halfTorus {n : ℕ} (S : Set (SpecialLinearGroup (Fin (n + 1)) F2))
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS3 : ∀ x ∈ S, x ^ 3 = 1) :
    ∃ A : SpecialLinearGroup (Fin (n + 1)) F2, ∀ x ∈ S, A⁻¹ * x * A ∈ halfTorus n := by
  obtain ⟨s, r, ε, A₀, hA₀⟩ := exists_frame_gf2
    (((↑) : SpecialLinearGroup (Fin (n + 1)) F2 → Matrix (Fin (n + 1)) (Fin (n + 1)) F2) '' S)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hSc x hx y hy))
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hS3 x hx))
  obtain ⟨π, hπ⟩ := exists_perm_nsMat_mem_halfTorus (n := n) ε
  refine ⟨A₀ * slPerm gf2_two π, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hA₀ x ⟨x, hx, rfl⟩
  have hM : ((A₀⁻¹ * x * A₀ : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = SLNS.nsMat ε rhoM k := by
    have h1 : ((A₀⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
        (A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = 1 := by
      exact congrArg (fun A : SpecialLinearGroup (Fin (n + 1)) F2 =>
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) (inv_mul_cancel A₀)
    calc ((A₀⁻¹ * x * A₀ : SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
        = ((A₀⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
            ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
              (A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) := by
          exact Matrix.mul_assoc _ _ _
      _ = ((A₀⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
            ((A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) * SLNS.nsMat ε rhoM k) := by rw [hk]
      _ = SLNS.nsMat ε rhoM k := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hconj := hπ k (A₀⁻¹ * x * A₀) hM
  have hrw : (A₀ * slPerm gf2_two π)⁻¹ * x * (A₀ * slPerm gf2_two π) =
      (slPerm gf2_two π)⁻¹ * (A₀⁻¹ * x * A₀) * slPerm gf2_two π := by group
  rw [hrw]
  exact hconj

end CFSG.StandardType.GGHalf

end
