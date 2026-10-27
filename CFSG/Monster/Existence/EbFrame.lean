module

public import CFSG.Monster.Existence.EbNative
public import Certificates.Certificate16030

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

theorem phi0_coordOf_qP (s A D : ℕ) : phi0 (coordOf (qP s A D)) = vecX (packP (false, A, D)) := by
  rw [vecX_packP, qP, coordOf_pauliQ]

theorem rhoEquiv_qP_mem_frameInv
    {s A D : ℕ} (h0 : packP (false, A, D) ≠ 0)
    (hq : qX (packP (false, A, D)) = false) (hs : isShortX (packP (false, A, D)) = false) :
    rhoEquiv (qP s A D) ∈ frameInv :=
  rhoEquiv_mem_frameInv_of_packed (packP_lt _) (phi0_coordOf_qP s A D) h0 hq hs

theorem rhoEquiv_qP_zero_three_sixty_mem_shortInv :
    rhoEquiv (qP 0 3 60) ∈ shortInv := by
  refine ⟨qP 0 3 60, ?_, rfl⟩
  have h : isShortX (packP (false, 3, 60)) = true := witness_packed_shortness.1
  rw [isShortX_iff (packP_lt _), ← phi0_coordOf_qP 0 3 60] at h
  exact h

theorem rhoEquiv_qP_one_sixty_sixty_mem_frameInv :
    rhoEquiv (qP 1 60 60) ∈ frameInv :=
  rhoEquiv_qP_mem_frameInv (by exact Certificates.certificate16030.1)
    (by exact Certificates.certificate16030.2.1) witness_packed_shortness.2.1

theorem rhoEquiv_qP_one_three_fortyeight_mem_frameInv :
    rhoEquiv (qP 1 3 48) ∈ frameInv :=
  rhoEquiv_qP_mem_frameInv (by exact Certificates.certificate16030.2.2.1)
    (by exact Certificates.certificate16030.2.2.2.1) witness_packed_shortness.2.2.1

theorem rhoEquiv_qP_one_734_zero_mem_frameInv :
    rhoEquiv (qP 1 734 0) ∈ frameInv :=
  rhoEquiv_qP_mem_frameInv (by exact Certificates.certificate16030.2.2.2.2.1)
    (by exact Certificates.certificate16030.2.2.2.2.2) witness_packed_shortness.2.2.2

theorem exists_Gmat_conj_rhoEquiv_qP_one_sixty_sixty :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = rhoEquiv (qP 1 60 60) :=
  exists_Gmat_conj_xmat rhoEquiv_qP_one_sixty_sixty_mem_frameInv

theorem exists_Gmat_conj_rhoEquiv_qP_one_three_fortyeight :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = rhoEquiv (qP 1 3 48) :=
  exists_Gmat_conj_xmat rhoEquiv_qP_one_three_fortyeight_mem_frameInv

theorem exists_Gmat_conj_rhoEquiv_qP_one_734_zero :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = rhoEquiv (qP 1 734 0) :=
  exists_Gmat_conj_xmat rhoEquiv_qP_one_734_zero_mem_frameInv

end CFSG.Monster.Existence
