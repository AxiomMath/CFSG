module

public import CFSG.GH74.KGroups.L34
public import CFSG.GH74.KGroups.L34AutInputs
import Certificates.Kernel.PermCent.KG5168Glue

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates CFSG.Sporadic.Schreier

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L34 in
open CFSG.Certificates CFSG.Sporadic.Schreier in
theorem certificate5168 : ((elemsT QA).all fun σ => !(decide (σ ^ 27 = 1)) || QP.sift σ 0 ||
    decide (((elemsT QP).filter (fun g => decide (g * σ = σ * g))).length % 9 ≠ 0)) = true := by
  rw [List.all_eq_true]
  intro σ hσ
  have hA := (mem_elemsT QA QA_ok σ).1 hσ
  by_cases h27 : σ ^ 27 = 1
  · by_cases h9 : ((elemsT QP).filter (fun g => decide (g * σ = σ * g))).length % 9 = 0
    · have hP := CFSG.Certificates.Kernel.PkCV.KGrp.K5168.outer3_mem_QP σ hA h27
        (by rw [card_inf_centralizer QP QP_ok σ]; exact Nat.dvd_of_mod_eq_zero h9)
      rw [mem_iff_sift QP QP_ok] at hP
      simp [hP]
    · simp [h9]
  · simp [h27]

end Certificates
