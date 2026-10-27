module

public import CFSG.Monster.B.TwoA.Census.CosetSquares
public import CFSG.Monster.B.Cbar.GenData
public meta import CFSG.Monster.B.TwoA.Census.CosetSquares
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public import Certificates.Certificate3053
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.B.Rep4371
  CFSG.Monster.B.Short

theorem bvec_three : bvec 24 3 = Pi.single 0 1 + Pi.single 1 1 := by decide

theorem deltaPair_zero_one : deltaPair 0 1 = toD 191 := by
  rw [deltaPair, ← bvec_three, mk_bvec_eq_toD]
  rfl

theorem rStar_eq : rStar = qP 0 0 191 := by
  rw [rStar, DQ_eq, deltaPair_zero_one, qP, pauliQ]
  congr 1
  refine SpinCoord.ext ?_ ?_ ?_
  · rfl
  · rw [toSC_a, pauli_a, toC_zero]
  · rfl

theorem tStar_eq : tStar = rhoEquiv (qP 0 0 191) := by
  rw [tStar, rStar_eq]

@[expose] def cSqrt :
    SpaceB ≃ₗ[ℚ] SpaceB := thetaEquiv (cosetPair 1 * rhoPair (qP 0 70 5))

theorem cSqrt_eq :
    cSqrt = rhoEquiv (qP 0 70 5) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [cSqrt, thetaEquiv_mul]
  rfl

theorem cSqrt_mem_Gvis :
    cSqrt ∈ Gvis := thetaEquiv_mem_Gvis _

theorem alpha_check : alphaN 1 (false, 70, 5) = (true, 70, 186) :=
  Certificates.certificate3053

theorem alpha_q :
    conjQ (cosetPair 1) (qP 0 70 5) = qP 1 70 186 := by
  rw [show qP 0 70 5 = pauliQ (false, 70, 5) from rfl, conjQ_cosetPair, alpha_check]
  rfl

theorem inv_mul_rhoPair_mul (p : Pvis) (r : Q) : p⁻¹ * rhoPair r * p = rhoPair (conjQ p r) := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show p.1.1⁻¹ * (r : GL SpinIdx ℚ) * p.1.1 = ((conjQ p r : Q) : GL SpinIdx ℚ)
    exact (coe_conjQ p r).symm
  · show p.1.2⁻¹ * 1 * p.1.2 = 1
    rw [mul_one, inv_mul_cancel]

theorem coset_sq_aux {P x y z : Pvis} (hP : P * P = 1)
    (hx : P⁻¹ * x * P = y) (hyx : y * x = z) : (P * x) * (P * x) = z := by
  have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP
  rw [← hyx, ← hx, hPinv]
  group

theorem qP_prod : qP 1 70 186 * qP 0 70 5 = qP 0 0 191 := by
  rw [qP_mul]
  rfl

theorem cSqrt_sq :
    cSqrt * cSqrt = tStar := by
  have hP : cosetPair 1 * cosetPair 1 = 1 := by
    rw [cosetPair_sq_of_ne_six (Or.inl rfl), pauliQ_sqPauli_one, map_one]
  have hq : conjQ (cosetPair 1) (qP 0 70 5) * qP 0 70 5 = qP 0 0 191 := by
    rw [alpha_q]
    exact qP_prod
  have hyx : rhoPair (conjQ (cosetPair 1) (qP 0 70 5)) * rhoPair (qP 0 70 5) =
      rhoPair (qP 0 0 191) :=
    (map_mul rhoPair _ _).symm.trans (congrArg rhoPair hq)
  have hsq : (cosetPair 1 * rhoPair (qP 0 70 5)) * (cosetPair 1 * rhoPair (qP 0 70 5)) =
      rhoPair (qP 0 0 191) :=
    coset_sq_aux hP (inv_mul_rhoPair_mul (cosetPair 1) (qP 0 70 5)) hyx
  rw [cSqrt, ← thetaEquiv_mul, hsq, tStar_eq]
  rfl

theorem cSqrt_sq' :
    cSqrt ^ 2 = tStar := by rw
    [sq, cSqrt_sq]

theorem orderOf_cSqrt :
    orderOf cSqrt = 4 := by
  have h4 : cSqrt ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, cSqrt_sq', sq, tStar_mul_self]
  have h2 : ¬cSqrt ^ 2 ^ 1 = 1 := by
    rw [pow_one, cSqrt_sq']
    exact tStar_ne_one
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
  simpa using this

theorem cSqrt_mem_Jstar :
    cSqrt ∈ Jstar := by
  refine ⟨cSqrt_mem_Gvis, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← cSqrt_sq, mul_assoc]

theorem short_centralizer_central_square_root :
    tStar = rhoEquiv (qP 0 0 191) ∧
    cSqrt = thetaEquiv (cosetPair 1 * rhoPair (qP 0 70 5)) ∧
    cSqrt = rhoEquiv (qP 0 70 5) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) ∧
    ((cosetRep 1 * cosetRep 1 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = 1 ∧
    conjQ (cosetPair 1) (qP 0 70 5) = qP 1 70 186 ∧
    cSqrt * cSqrt = tStar ∧ orderOf cSqrt = 4 ∧ cSqrt ∈ Jstar ∧ Jstar ≤ Cgen ∧
    cSqrt ∈ Cgen :=
  ⟨tStar_eq, rfl, cSqrt_eq, cosetRep_sq.1, alpha_q, cSqrt_sq, orderOf_cSqrt, cSqrt_mem_Jstar,
    Jstar_le_Cgen, Jstar_le_Cgen cSqrt_mem_Jstar⟩

end CFSG.Monster.B.TwoA.Census
