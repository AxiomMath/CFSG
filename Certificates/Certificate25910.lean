module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3S6Check
import CFSG.Certificates.Kernel.PermCent.GHFast
import CFSG.Certificates.Kernel.F3152.SortSound

public section

open CFSG.EvenSporadicStandard.M22Std.S6Check

namespace CertificateChecks.Batch25910

open CFSG.EvenSporadicStandard.M22Std.S6Check

private def code6 (σ : Equiv.Perm (Fin 6)) : ℕ :=
  (List.finRange 6).foldr (fun i acc => acc * 8 + (σ i : ℕ)) 0

open CFSG.Certificates.Kernel.PkCV in
private theorem allPL6_nodup : (allPL 6).Nodup :=
  List.Nodup.of_map code6 (CFSG.KS.F3152.nodup_of_sortedK (by decide +kernel))

open CFSG.Certificates.Kernel.PkCV in
private theorem cS6_eq (u : Equiv.Perm (Fin 6)) :
    cS6 u = ((allPL 6).filter fun c => permBEq (c * u) (u * c)).length := by
  unfold cS6
  rw [card_subtype_eq_length allPL6_nodup]
  simp only [decide_eq_permBEq]

open CFSG.Certificates.Kernel.PkCV in
private theorem cA6_eq (u : Equiv.Perm (Fin 6)) :
    cA6 u = (((allPL 6).filter fun c => decide (Equiv.Perm.sign c = 1)).filter
      fun c => permBEq (c * u) (u * c)).length := by
  unfold cA6
  rw [Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
      (· ∈ alternatingGroup (Fin 6)) fun c => c * u = u * c).trans
      (Equiv.subtypeEquivRight fun x => (by rw [Equiv.Perm.mem_alternatingGroup, and_comm] :
        x ∈ alternatingGroup (Fin 6) ∧ x * u = u * x ↔
          x * u = u * x ∧ Equiv.Perm.sign x = 1))), card_subtype_eq_length allPL6_nodup,
    List.filter_filter]
  simp only [Bool.decide_and, decide_eq_permBEq]

set_option maxHeartbeats 0 in
open scoped CFSG.Certificates.Kernel.PkCV.FastDecide in
theorem prop1 : S6Prop1 := by
  unfold S6Prop1
  simp only [cS6_eq]
  decide +kernel

set_option maxHeartbeats 0 in
open CFSG.Certificates.Kernel.PkCV in
theorem prop2 : S6Prop2 := by
  unfold S6Prop2 invData
  simp only [cA6_eq, univ_filter_eq_allPL, decide_eq_permBEq]
  decide +kernel

theorem check_0 : s6Check = true := decide_eq_true ⟨prop1, prop2⟩

end CertificateChecks.Batch25910

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.S6Check in
theorem certificate25910 : s6Check = true := CertificateChecks.Batch25910.check_0

end Certificates

