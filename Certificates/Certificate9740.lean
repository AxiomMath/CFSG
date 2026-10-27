module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import CFSG.GH74.KGroups.M11Inputs
import CFSG.Certificates.Kernel.PermCent.ConjInv
import CFSG.Certificates.Kernel.PermCent.GoodCSound
import CFSG.GH74.KGroups.M11
import Certificates.Kernel.PermCent.K9740R

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkCV.ConjInv
  CFSG.Certificates.Kernel.PkCV.Good CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.Sporadic.Mathieu

namespace Certificates

theorem certificate9740 : CFSG.ClassicalInvolution.Q3.TA3.Check.goodCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.M11.Q) = true := by
  have hL := mem_elemsT Q Q_ok
  refine goodCheck_of_invol Q.originalSubgroup hL 100 fun t ht h2 h1 => ?_
  rw [Q_subgroup] at ht
  obtain ⟨g, hg, rfl⟩ := invol_conj t ht (orderOf_eq_prime h2 h1)
  rw [← Q_subgroup] at hg
  obtain ⟨hg1, hg2⟩ := conj_mem_list Q.originalSubgroup hL hg
  rw [goodAt_conj hg1 hg2, elemsT_eq_elemsC, eq_ev_cOf m11gA, goodAt]
  have hc : centB ((elemsC Q).map ev) (ev (cOf m11gA)) = (centB (elemsC Q) (cOf m11gA)).map ev :=
    centB_map (evHom 11) ev_injective _ _
  have h3 : noOddB 100 ((centB (elemsC Q) (cOf m11gA)).map ev) =
      noOddB 100 (centB (elemsC Q) (cOf m11gA)) := noOddB_map (evHom 11) ev_injective _ _
  have h4 : pairsB (ev (cOf m11gA)) ((centB (elemsC Q) (cOf m11gA)).map ev) =
      pairsB (cOf m11gA) (centB (elemsC Q) (cOf m11gA)) := pairsB_map (evHom 11) ev_injective _ _
  rw [hc, h3, h4, centB_C, noOddB_C]
  exact K9740R.k9740r

end Certificates
