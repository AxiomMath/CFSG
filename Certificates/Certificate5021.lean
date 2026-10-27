module

public import CFSG.GH74.E2.Q8C2Check
public import CFSG.GH74.KGroups.U33
import CFSG.Certificates.Kernel.PermCent.ConjInv
import Certificates.Kernel.PermCent.K5021R
public import Certificates.Data.Kernel.PermCent.KGrpC3

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.GH74.E2 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkCV.ConjInv
  CFSG.ClassicalInvolution.Q3.TA3.Check

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.GH74.KGroups in
theorem certificate5021 : q8c2free (elemsT U33.QA) = true := by
  have hL := mem_elemsT QA QA_ok
  refine q8c2free_of_invol QA.originalSubgroup hL fun t ht h2 h1 => ?_
  rw [QA_closure] at ht
  obtain ⟨r, hr, g, hg, rfl⟩ := invol_A t ht (orderOf_eq_prime h2 h1)
  rw [← QA_closure] at hg
  rw [q8c2At_conj QA.originalSubgroup hL hg, eq_ev_cOf r]
  have hρ : cOf r ∈ K5021R.reps := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons.2 (Or.inl rfl)
    · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  have hk := List.all_eq_true.1 K5021R.k5021r (cOf r) hρ
  have hc : centB ((elemsC QA).map ev) (ev (cOf r)) = (centB (elemsC QA) (cOf r)).map ev :=
    centB_map (evHom 28) ev_injective _ _
  rw [q8c2At, elemsT_eq_elemsC, hc, q8c2at_C, centB]
  simp only [comm_fast]
  exact hk

end Certificates
