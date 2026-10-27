module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsPassDefs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K441621
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.OddStandard.SmallF3.L33
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L33T

namespace Certificates

private theorem sqOneB_ev (g : CV 26) : sqOneB (ev g) = decide (g * g = 1) := by
  rw [sqOneB, allFin_sq, ev_mul', one_eq_ev, decide_ev_eq]

private theorem isOneB_ev (g : CV 26) : isOneB (ev g) = decide (g = 1) := by
  rw [isOneB, allFin_id, one_eq_ev, decide_ev_eq]

private theorem commB_ev (g : CV 26) (σ : Equiv.Perm (Fin 26)) :
    commB (ev g) σ = decide (g * cOf σ = cOf σ * g) := by
  rw [commB, allFin_comm, decide_comm_ev]

private theorem conjImg_ev (g : CV 26) (e : Equiv.Perm (Fin 26)) :
    conjImg (ev g) e = CFSG.OddStandard.SmallF3.L33.img (ev g * e * (ev g)⁻¹) := rfl

private theorem contains_img (L : List (Equiv.Perm (Fin 26))) (σ : Equiv.Perm (Fin 26)) :
    (L.map CFSG.OddStandard.SmallF3.L33.img).contains (CFSG.OddStandard.SmallF3.L33.img σ) = decide (σ ∈ L) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff, List.mem_map]
  exact ⟨fun ⟨τ, hτ, h⟩ => (map_finRange_eq_iff τ σ).1 h ▸ hτ, fun h => ⟨σ, h, rfl⟩⟩

private theorem beq_img (σ τ : Equiv.Perm (Fin 26)) :
    (CFSG.OddStandard.SmallF3.L33.img σ == CFSG.OddStandard.SmallF3.L33.img τ) = decide (σ = τ) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact map_finRange_eq_iff σ τ

private theorem norm1B_ev (g : CV 26) : norm1B (ev g) = norm1C g := by
  unfold norm1B norm1C e1Img
  simp only [conjImg_ev, contains_img, beq_img, decide_conj_mem_ev, decide_conj_ev, e1L]
  rfl

private theorem norm2B_ev (g : CV 26) : norm2B (ev g) = norm2C g := by
  unfold norm2B norm2C e2Img
  simp only [conjImg_ev, contains_img, beq_img, decide_conj_mem_ev, decide_conj_ev, e2L]
  rfl

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.OddStandard.SmallF3.L33 in
theorem certificate441621 : (elemsT QA).length = 11232
    ∧ (elemsT QA).countP innerInvB = 117
    ∧ (elemsT QA).countP outerInvB = 234
    ∧ (elemsT QA).countP centB = 48
    ∧ (elemsT QA).countP centPB = 24
    ∧ (elemsT QA).all norm1B = true
    ∧ (elemsT QA).all norm2B = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := k441621
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [elemsT_eq_elemsC]
  · rw [List.length_map]
    exact h1
  · rw [List.countP_map]
    convert h2 using 2
    funext g
    simp only [Function.comp_apply, innerInvB, innerC, sqOneB_ev, isOneB_ev, sift_ev]
  · rw [List.countP_map]
    convert h3 using 2
    funext g
    simp only [Function.comp_apply, outerInvB, outerC, sqOneB_ev, sift_ev]
  · rw [List.countP_map]
    convert h4 using 2
    funext g
    simp only [Function.comp_apply, centB, centKC, commB_ev]
  · rw [List.countP_map]
    convert h5 using 2
    funext g
    simp only [Function.comp_apply, centPB, centPC, commB_ev, sift_ev]
  · rw [List.all_map]
    convert h6 using 2
    funext g
    simp only [Function.comp_apply, norm1B_ev]
  · rw [List.all_map]
    convert h7 using 2
    funext g
    simp only [Function.comp_apply, norm2B_ev]

end Certificates
