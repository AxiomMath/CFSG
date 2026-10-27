module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import CFSG.GH74.KGroups.U33Inputs
import CFSG.Certificates.Kernel.PermCent.ConjInv
import CFSG.Certificates.Kernel.PermCent.GoodCSound
import CFSG.GH74.KGroups.U33
import Certificates.Kernel.PermCent.K9743R

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates.Kernel.PkCV.ConjInv
  CFSG.Certificates.Kernel.PkCV.Good CFSG.ClassicalInvolution.Q3.TA3.Check

namespace Certificates

theorem certificate9743 : CFSG.ClassicalInvolution.Q3.TA3.Check.goodCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QP) = true := by
  have hL := mem_elemsT QP QP_ok
  have hP : ∀ σ ∈ Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28))),
      ∀ x ∈ elemsT QP, σ * x * σ⁻¹ ∈ elemsT QP := by
    intro σ hσ x hx
    rw [hL, QP_closure] at hx ⊢
    exact conj_AP σ hσ x hx
  refine goodCheck_of_invol QP.originalSubgroup hL 100 fun t ht h2 h1 => ?_
  rw [QP_closure] at ht
  obtain ⟨g, hg, rfl⟩ := invol_P t ht (orderOf_eq_prime h2 h1)
  have h2' : ∀ x ∈ elemsT QP, g⁻¹ * x * g ∈ elemsT QP := fun x hx => by
    have h := hP g⁻¹ (inv_mem hg) x hx
    rwa [inv_inv] at h
  rw [goodAt_conj (hP g hg) h2', elemsT_eq_elemsC, eq_ev_cOf pu, goodAt]
  have hc : centB ((elemsC QP).map ev) (ev (cOf pu)) = (centB (elemsC QP) (cOf pu)).map ev :=
    centB_map (evHom 28) ev_injective _ _
  have h3 : noOddB 100 ((centB (elemsC QP) (cOf pu)).map ev) =
      noOddB 100 (centB (elemsC QP) (cOf pu)) := noOddB_map (evHom 28) ev_injective _ _
  have h4 : pairsB (ev (cOf pu)) ((centB (elemsC QP) (cOf pu)).map ev) =
      pairsB (cOf pu) (centB (elemsC QP) (cOf pu)) := pairsB_map (evHom 28) ev_injective _ _
  rw [hc, h3, h4, centB_C, noOddB_C]
  exact K9743R.k9743r

end Certificates
