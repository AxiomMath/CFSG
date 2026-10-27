module

public import CFSG.Monster.Generated.Data
public import CFSG.Monster.Visible.SignCompat.Triality

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Generated

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Griess CFSG.Monster.Visible Matrix

@[expose] def greyZero : C := ⟨g 0, g_mem_C 0⟩

theorem coe_greyZero : (greyZero : Fin 24 → ZMod 2) = g 0 := rfl

@[expose] noncomputable def greyTrans : SpaceB ≃ₗ[ℚ] SpaceB :=
  rhoEquiv ⟨TU greyZero, TU_mem_Q greyZero⟩

namespace GreyEscape

theorem greyZero_apply_zero : (greyZero : Fin 24 → ZMod 2) 0 = 0 := by
  rw [coe_greyZero]
  decide

theorem greyZero_apply_one : (greyZero : Fin 24 → ZMod 2) 1 = 1 := by
  rw [coe_greyZero]
  decide

theorem P_greyZero : P (greyZero : Fin 24 → ZMod 2) = 0 := by
  rw [coe_greyZero]
  decide

theorem greyVec_single_zero : greyVec (Pi.single 0 1) = 0 := by decide

theorem coe_greyZero_eq_sum :
    (greyZero : Fin 24 → ZMod 2) =
      ∑ j, (Pi.single (0 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) j • g j := by
  rw [coe_greyZero, Fintype.sum_eq_single 0 (fun j hj => by rw [Pi.single_eq_of_ne hj, zero_smul]),
    Pi.single_eq_same, one_smul]

theorem θ_greyZero (f : C) : θ greyZero f = 0 := by
  rw [θ_grey _ greyZero f coe_greyZero_eq_sum, greyVec_single_zero, dotProduct_zero]

theorem thetaD_greyZero : thetaD greyZero = 0 :=
  (thetaD_unique fun u => by rw [map_zero, θ_greyZero]).symm

theorem TU_greyZero : TU greyZero = XU ⟨greyZero, 0⟩ := by
  rw [TU, thetaD_greyZero, DU_zero, mul_one]

theorem TQ_greyZero : (⟨TU greyZero, TU_mem_Q greyZero⟩ : Q) = XQ ⟨greyZero, 0⟩ :=
  Subtype.ext TU_greyZero

theorem greyTrans_eq : greyTrans = rhoEquiv (XQ ⟨greyZero, 0⟩) := by
  rw [greyTrans, TQ_greyZero]

theorem greyTrans_conj_eq :
    tauB * greyTrans * tauB⁻¹ = thetaEquiv (signLiftPair ⟨greyZero, 0⟩) := by
  rw [greyTrans_eq, thetaEquiv_signLiftPair]

theorem greyTrans_mem_Qmat : greyTrans ∈ Qmat := mem_rhoQ.2 ⟨_, rfl⟩

theorem greyTrans_conj_mem_Hmat : tauB * greyTrans * tauB⁻¹ ∈ Hmat := by
  rw [greyTrans_conj_eq]
  exact thetaEquiv_mem_Gvis _

theorem coe_basisA_zero_one :
    ((basisA s(0, 1) : symMat) : Matrix (Fin 24) (Fin 24) ℚ) =
      Matrix.single 0 1 1 + Matrix.single 1 0 1 := by
  rw [coe_basisA, ite_eq_right (by decide)]

theorem greyTrans_conj_A01 :
    (tauB * greyTrans * tauB⁻¹) (basisA s(0, 1), 0, 0) = -(basisA s(0, 1), 0, 0) := by
  rw [greyTrans_conj_eq, thetaEquiv_apply, SignCompat.theta_sign_A,
    SignCompat.thetaA_gmat_basisA, greyZero_apply_zero, greyZero_apply_one, zero_add,
    show sgn 1 = -1 from rfl, SignCompat.mk_A_smul]
  exact neg_one_smul ℚ ((basisA s(0, 1), 0, 0) : SpaceB)

theorem greyTrans_conj_not_mem_Qmat : tauB * greyTrans * tauB⁻¹ ∉ Qmat := by
  intro h
  obtain ⟨r, hr⟩ := mem_rhoQ.1 h
  have h1 := greyTrans_conj_A01
  rw [← hr, rhoEquiv_symMat] at h1
  have h2 : (2 : ℚ) • ((basisA s(0, 1), 0, 0) : SpaceB) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel _
  have h3 : ((basisA s(0, 1), 0, 0) : SpaceB) = 0 := (smul_eq_zero.1 h2).resolve_left two_ne_zero
  exact basisA.ne_zero s(0, 1) (congrArg Prod.fst h3)

end GreyEscape

open GreyEscape

theorem grey_translation_triality_escape :
    (greyZero : Fin 24 → ZMod 2) = g 0 ∧ thetaD greyZero = 0 ∧
    P (greyZero : Fin 24 → ZMod 2) = 0 ∧ TU greyZero = XU ⟨greyZero, 0⟩ ∧
    greyTrans = rhoEquiv ⟨TU greyZero, TU_mem_Q greyZero⟩ ∧
    greyTrans ∈ Qmat ∧ tauB * greyTrans * tauB⁻¹ ∈ Hmat ∧ tauB * greyTrans * tauB⁻¹ ∉ Qmat ∧
    ((basisA s(0, 1) : symMat) : Matrix (Fin 24) (Fin 24) ℚ) =
      Matrix.single 0 1 1 + Matrix.single 1 0 1 ∧
    (tauB * greyTrans * tauB⁻¹) (basisA s(0, 1), 0, 0) = -(basisA s(0, 1), 0, 0) :=
  ⟨coe_greyZero, thetaD_greyZero, P_greyZero, TU_greyZero, rfl, greyTrans_mem_Qmat,
    greyTrans_conj_mem_Hmat, greyTrans_conj_not_mem_Qmat, coe_basisA_zero_one,
    greyTrans_conj_A01⟩

end CFSG.Monster.Generated
