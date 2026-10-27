module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

@[expose] def rootTorusUnits {K : Type} [Field K] (r : ℕ) (c : Kˣ) : Fin r → Kˣ :=
  fun i => if (i : ℕ) = 0 then c else if (i : ℕ) = 1 then c⁻¹ else 1

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem rootTorusUnits_zero [NeZero r] (c : Kˣ) : rootTorusUnits r c (0 : Fin r) = c := by
  simp [rootTorusUnits]

theorem tailDiag_hypVec_inl (t : Fin r → Kˣ) (h : A ≃ₗ[K] A) (i : Fin r) :
    tailDiag r t h (hypVec K A (Sum.inl i)) = ((t i : Kˣ) : K) • hypVec K A (Sum.inl i) := by
  rw [hypVec, tailDiag_apply]
  change (torusElt r K t (Pi.single (Sum.inl i) 1), h 0) =
    (((t i : Kˣ) : K) • Pi.single (Sum.inl i) 1, ((t i : Kˣ) : K) • (0 : A))
  rw [map_zero, smul_zero]
  congr 1
  funext c
  rw [torusElt_apply, Pi.smul_apply]
  rcases c with j | j
  · by_cases hji : j = i
    · rw [hji]; simp
    · simp [hji, Sum.inl.injEq]
  · simp [Sum.inl_ne_inr]

theorem tailDiag_rootTorusUnits_hypVec [NeZero r] (c : Kˣ) (h : A ≃ₗ[K] A) :
    tailDiag r (rootTorusUnits r c) h (hypVec K A (Sum.inl (0 : Fin r))) =
      (c : K) • hypVec K A (Sum.inl (0 : Fin r)) := by
  rw [tailDiag_hypVec_inl, rootTorusUnits_zero]

theorem mem_tailBorel_of_eq_tailDiag {g : ↥(orthElementaryGroup (quadTail r qA))}
    {t : Fin r → Kˣ} (hg : g.val = tailDiag r t 1) : g.val ∈ tailBorel r qA :=
  tailTorus_le_tailBorel (mem_tailTorus.2 ⟨g.2, t, 1, one_mem _, hg.symm⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
