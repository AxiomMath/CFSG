module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Model
public import CFSG.GH74.KGroups.U33
public import Certificates.Certificate1037402

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 Gs03U33

theorem gs03AlphaU33_holds :
    GS03AlphaU33 := by
  classical
  intro G _ _ S hS hC hlie x hx
  haveI : S.Normal := hS
  obtain ⟨e⟩ := U33.equiv_of_lieModel hlie
  obtain ⟨M, hP, hA⟩ := U33.autModel e
  have hcert : u33GenCheck () = true := Certificates.certificate1037402
  simp only [u33GenCheck, Bool.and_eq_true_iff] at hcert
  obtain ⟨h1, h2⟩ := hcert
  have h1' : u33Classes.map (fun c => c.1) = [pu, pt2] := of_decide_eq_true h1
  have hgens : QP.originalSubgroup ≤ Subgroup.closure {x | x ∈ [pa, pb]} := by
    rw [U33.QP_closure]
    exact Subgroup.closure_mono fun z hz => by simpa using hz
  have hcov : ∀ g ∈ M.A, g * g = 1 → g ≠ 1 →
      ∃ r ∈ u33Classes.map (fun c => c.1), ∃ h ∈ M.A, g = h * r * h⁻¹ := by
    intro g hgA' hgg hgne
    have hgA : g ∈ Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28))) := by
      have h' := hgA'
      rw [hA, U33.QA_closure] at h'
      exact h'
    have hord : orderOf g = 2 := orderOf_eq_prime (by rwa [pow_two]) hgne
    obtain ⟨r, hr, hconj⟩ := U33.invol_A g hgA hord
    simp only [conjSet, Set.mem_setOf_eq] at hconj
    obtain ⟨h, hh, hgh⟩ := hconj
    refine ⟨r, ?_, h, ?_, hgh⟩
    · rw [h1']; exact hr
    · rw [hA, U33.QA_closure]; exact hh
  have hcls : ∀ r ∈ u33Classes.map (fun c => c.1), ∃ s : Fin 4 → M.P,
      M.P ≤ Subgroup.closure
        (Set.range fun i => ((s i : M.P) : Equiv.Perm (Fin 28))⁻¹ * r *
          ((s i : M.P) : Equiv.Perm (Fin 28))) := by
    intro r hr
    rw [hP]
    exact gs03_classesCheck_sound QP U33.QP_ok [pa, pb] hgens h2 r hr
  have hPA : M.P ≤ M.A := by
    rw [hP, hA, U33.QP_closure, U33.QA_closure]
    exact U33.P_le_A
  have hag : AutGenBound ↥S 4 (fun _ => True) :=
    gs03_autGenBound_of_classes M hPA (u33Classes.map fun c => c.1) hcov hcls
  obtain ⟨T, hTcard, hTconj, hTgen⟩ :=
    gs03_of_autGenBound hag S hC (MulEquiv.refl ↥S) hx trivial
  exact ⟨T, hTcard, hTconj, hTgen⟩

end CFSG.LocalAnalysis.WeakClosure81
