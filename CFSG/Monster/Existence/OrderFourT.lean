module

public import CFSG.Monster.Existence.TwoPoint.LeechMG
public import CFSG.Monster.Existence.EbNative
public import Certificates.Certificate16031

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

theorem alphaOne_pauli_zero_zero_four :
    alphaN 1 (false, 0, 4) = (false, 3, 56) :=
  Certificates.certificate16031.1

theorem mul_alphaOne_qP_zero_zero_four :
    qP 0 0 4 * cosetW 1 * conjQ (cosetPair 1) (qP 0 0 4) = qP 0 3 60 := by
  have h1 : cosetW 1 = 1 := pauliQ_sqPauli_one
  have h2 : conjQ (cosetPair 1) (qP 0 0 4) = qP 0 3 56 := by
    change conjQ (cosetPair 1) (pauliQ (false, 0, 4)) = pauliQ (false, 3, 56)
    rw [conjQ_cosetPair, alphaOne_pauli_zero_zero_four]
  have h3 : Model.Pauli.mul (false, 0, 4) (false, 3, 56) = (false, 3, 60) :=
    Certificates.certificate16031.2
  rw [h1, h2, mul_one]
  change pauliQ (false, 0, 4) * pauliQ (false, 3, 56) = pauliQ (false, 3, 60)
  rw [← pauliQ_mul, h3]

theorem sq_cosetRep_one_mul_rho :
    (cosetRep 1 * rhoGvis (qP 0 0 4)) * (cosetRep 1 * rhoGvis (qP 0 0 4)) =
      rhoGvis (qP 0 3 60) := by
  rw [mul_rho_sq (Or.inl rfl), mul_alphaOne_qP_zero_zero_four]

theorem isShortCoord_qP_zero_three_sixty :
    IsShortCoord (coordOf (qP 0 3 60)) := by
  have h : shortEnc (pauliEnc 0 3 60) = true := witness_packed_shortness.1
  have h' := (shortEnc_iff (pauliEnc 0 3 60)).1 h
  rwa [qOfEnc_eq_qP (s := 0) (A := 3) (D := 60) (by norm_num) (by norm_num) (by norm_num)
    rfl] at h'

@[expose] noncomputable def wOrderFourRep :
    MGriess :=
  ⟨((cosetRep 1 * rhoGvis (qP 0 0 4) : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB),
    Gvis_le_AutO (cosetRep 1 * rhoGvis (qP 0 0 4)).2⟩

theorem wOrderFourRep_mul_self :
    wOrderFourRep * wOrderFourRep = rhoGriess (qP 0 3 60) := by
  have h := congrArg Subtype.val sq_cosetRep_one_mul_rho
  exact Subtype.ext h

theorem exists_sq_eq_tGriess :
    ∃ w ∈ cent tGriess, w * w = tGriess := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (leech_isConj_tGriess_rhoGriess isShortCoord_qP_zero_three_sixty)
  have hw : (c⁻¹ * wOrderFourRep * c) * (c⁻¹ * wOrderFourRep * c) = tGriess := by
    calc (c⁻¹ * wOrderFourRep * c) * (c⁻¹ * wOrderFourRep * c)
        = c⁻¹ * (wOrderFourRep * wOrderFourRep) * c := by group
      _ = c⁻¹ * (c * tGriess * c⁻¹) * c := by rw [wOrderFourRep_mul_self, hc]
      _ = tGriess := by group
  refine ⟨c⁻¹ * wOrderFourRep * c, ?_, hw⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (c⁻¹ * wOrderFourRep * c) * tGriess
      = (c⁻¹ * wOrderFourRep * c) * ((c⁻¹ * wOrderFourRep * c) * (c⁻¹ * wOrderFourRep * c)) := by
        rw [hw]
    _ = (c⁻¹ * wOrderFourRep * c) * (c⁻¹ * wOrderFourRep * c) * (c⁻¹ * wOrderFourRep * c) :=
        (mul_assoc _ _ _).symm
    _ = tGriess * (c⁻¹ * wOrderFourRep * c) := by rw [hw]

theorem exists_orderOf_four_sq_eq_tGriess :
    ∃ w ∈ cent tGriess, w * w = tGriess ∧ orderOf w = 4 := by
  obtain ⟨w, hw, hsq⟩ := exists_sq_eq_tGriess
  refine ⟨w, hw, hsq, leech_orderOf_eq_four_of_sq ((sq w).trans hsq) tGriess_mul_self ?_⟩
  intro h
  have := orderOf_tGriess
  rw [h, orderOf_one] at this
  omega

end CFSG.Monster.Existence
