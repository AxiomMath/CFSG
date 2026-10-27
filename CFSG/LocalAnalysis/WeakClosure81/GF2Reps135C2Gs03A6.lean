module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Model
public import CFSG.GH74.KGroups.A6
public import Certificates.Certificate1037401

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.KGroups CFSG.Sporadic.Schreier

private theorem gs03_a6_qp_le_qa :
    A6.QP.originalSubgroup ≤ A6.QA.originalSubgroup := by
  have hA : A6.QA.originalSubgroup =
      Subgroup.closure {g | g ∈ [A6.pa, A6.pb, A6.sg0, A6.sg1]} := by
    rw [A6.QA, certificate_originalSubgroup]
  rw [A6.QP_closure, Subgroup.closure_le, hA]
  rintro x (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem gs03AlphaA6_holds :
    GS03AlphaA6 := by
  classical
  intro G _ _ S hS hC hAlt x hx
  haveI : S.Normal := hS
  obtain ⟨e⟩ := A6.equiv_of_alt6 hAlt
  obtain ⟨M, hP, hA⟩ := A6.autModel e
  have hcheck := Certificates.certificate1037401
  rw [Gs03A6.a6GenCheck] at hcheck
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  have hcov : ∀ g ∈ M.A, g * g = 1 → g ≠ 1 →
      ∃ r ∈ Gs03A6.a6Classes.map (fun c => c.1), ∃ h ∈ M.A, g = h * r * h⁻¹ := by
    rw [hA]
    exact gs03_coverCheck_sound A6.QA A6.QA_ok h1
  have hcls : ∀ r ∈ Gs03A6.a6Classes.map (fun c => c.1),
      ∃ s : Fin 5 → M.P, M.P ≤ Subgroup.closure
        (Set.range fun i => ((s i : M.P) : Equiv.Perm (Fin 10))⁻¹ * r *
          ((s i : M.P) : Equiv.Perm (Fin 10))) := by
    intro r hr
    have hgens : A6.QP.originalSubgroup ≤ Subgroup.closure {z | z ∈ [A6.pa, A6.pb]} := by
      rw [A6.QP_closure]
      apply Subgroup.closure_mono
      intro z hz
      simpa using hz
    have hs := gs03_classesCheck_sound A6.QP A6.QP_ok [A6.pa, A6.pb] hgens h2
    exact hP.symm ▸ hs r hr
  have hPA : M.P ≤ M.A := by
    rw [hP, hA]
    exact gs03_a6_qp_le_qa
  have hag : AutGenBound ↥S 5 (fun _ => True) :=
    gs03_autGenBound_of_classes M hPA (Gs03A6.a6Classes.map fun c => c.1) hcov hcls
  exact gs03_of_autGenBound hag S hC (MulEquiv.refl _) hx trivial

end CFSG.LocalAnalysis.WeakClosure81
