module

public import CFSG.GH74.E2.Q8C2Check
public import CFSG.GH74.KGroups.M11
import CFSG.Certificates.Kernel.PermCent.ConjInv
import Certificates.Kernel.PermCent.K5013R
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.Kernel.PermCent.KGrpC3

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.GH74.E2 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkCV.ConjInv
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.Sporadic.Mathieu

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.GH74.KGroups in
theorem certificate5013 : q8c2free (elemsT M11.Q) = true := by
  have hL := mem_elemsT Q Q_ok
  refine q8c2free_of_invol Q.originalSubgroup hL fun t ht h2 h1 => ?_
  rw [Q_subgroup] at ht
  obtain ⟨g, hg, rfl⟩ := invol_conj t ht (orderOf_eq_prime h2 h1)
  rw [← Q_subgroup] at hg
  rw [q8c2At_conj Q.originalSubgroup hL hg, eq_ev_cOf m11gA]
  have hc : centB ((elemsC Q).map ev) (ev (cOf m11gA)) =
      (centB (elemsC Q) (cOf m11gA)).map ev :=
    centB_map (evHom 11) ev_injective _ _
  rw [q8c2At, elemsT_eq_elemsC, hc, q8c2at_C, centB]
  simp only [comm_fast]
  exact K5013R.k5013r

end Certificates
