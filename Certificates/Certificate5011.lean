module

public import CFSG.GH74.E2.Q8C2Check
public import CFSG.GH74.KGroups.L33
import CFSG.Certificates.Kernel.PermCent.ConjInv
import Certificates.Kernel.PermCent.K5011R
import Certificates.Kernel.PermCent.KL33Glue
public import Certificates.Data.Kernel.PermCent.KGrpC3

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.GH74.E2 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkCV.ConjInv
  CFSG.ClassicalInvolution.Q3.TA3.Check

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.GH74.KGroups in
theorem certificate5011 : q8c2free (elemsT L33.QA) = true := by
  have hL := mem_elemsT QA QA_ok
  refine q8c2free_of_invol QA.originalSubgroup hL fun c hc h2 h1 => ?_
  refine L33R.Glue.l33_invol (fun x => q8c2At (elemsT QA) x = true)
    (fun g hg x _ h => by rwa [q8c2At_conj QA.originalSubgroup hL hg] at h) (fun ρ hρ => ?_)
    c hc h2 h1
  have hk := List.all_eq_true.1 K5011R.k5011r ρ hρ
  have hc : centB ((elemsC QA).map ev) (ev ρ) = (centB (elemsC QA) ρ).map ev :=
    centB_map (evHom 26) ev_injective _ _
  rw [q8c2At, elemsT_eq_elemsC, hc, q8c2at_C, centB]
  simp only [comm_fast]
  exact hk

end Certificates
