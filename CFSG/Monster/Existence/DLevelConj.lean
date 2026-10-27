module

public import CFSG.Monster.Existence.DLevel
public import CFSG.Monster.B.Rep4371.PacketGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.Rep4371

theorem rTwo_eq_pauliQ : rTwo = pauliQ (false, 0, 127) := by
  have hd : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((2 : Fin 24) : ℕ)) = 127 := by decide
  have h := pauliQ_minus (i := 0) (j := 2) (by decide)
  rw [hd] at h
  rw [rTwo, h]
  rfl

theorem qElt_one_mul_rStar_eq : qElt 1 * Short.rStar = pauliQ (false, 3, 191) := by
  have h : Model.Pauli.mul (Model.qPauli ((1 : Fin 23) : ℕ)) (false, 0, 191) = (false, 3, 191) := by
    decide
  rw [qElt_eq, CFSG.Monster.B.rStar_eq, ← pauliQ_mul, h]

theorem conjQ_hPair_eleven (y : Model.Pauli) :
    conjQ (hPair 11) (pauliQ y) = pauliQ (Model.conjPermN Model.recPerms[11]! y) := by
  rw [hPair_of_lt_twelve (show ((11 : Fin 24) : ℕ) < 12 by decide), permPair,
    conjQ_perm_toQ _ (repPerm_recPerm 11 (by decide))]
  rfl

theorem conjQ_hPair_twenty_three (y : Model.Pauli) :
    conjQ (hPair 23) (pauliQ y) = pauliQ (Model.conjYN 1 (Model.conjXiN y)) := by
  rw [hPair_xi]
  show conjQ (xiPair * signPair 1) (pauliQ y) = _
  rw [conjQ_mul]
  exact (congrArg (conjQ (signPair 1)) (conjQ_xi_toQ _)).trans (conjQ_sign_toQ 1 _)

theorem conjQ_hPair_twenty (y : Model.Pauli) :
    conjQ (hPair 20) (pauliQ y) = pauliQ (Model.conjYN 512 y) := by
  rw [hPair_of_codeSign (show 12 ≤ ((20 : Fin 24) : ℕ) by decide)
    (show ((20 : Fin 24) : ℕ) < 23 by decide),
    conjQ_codeSign_pauliQ (recCode_eq (show 12 ≤ ((20 : Fin 24) : ℕ) by decide)
      (show ((20 : Fin 24) : ℕ) < 23 by decide))]
  rfl

theorem conjPermN_eleven : Model.conjPermN Model.recPerms[11]! (false, 0, 127) = (false, 0, 387) := by
  decide +kernel

theorem conjXi_step : Model.conjYN 1 (Model.conjXiN (false, 0, 387)) = (false, 60, 447) := by
  decide +kernel

theorem conjYN_step : Model.conjYN 512 (false, 60, 447) = (false, 3, 191) := by
  decide +kernel

@[expose] noncomputable def cConj : SpaceB ≃ₗ[ℚ] SpaceB := hElt 20 * hElt 23 * hElt 11

theorem cConj_mem_Cgen : cConj ∈ Cgen :=
  Cgen.mul_mem (Cgen.mul_mem (hElt_mem_Cgen 20) (hElt_mem_Cgen 23)) (hElt_mem_Cgen 11)

theorem conj_uStar : cConj * uStar * cConj⁻¹ = rhoEquiv (qElt 1) * tStar := by
  have h11 : hElt 11 * uStar * (hElt 11)⁻¹ = rhoEquiv (pauliQ (false, 0, 387)) := by
    rw [uStar, rTwo_eq_pauliQ]
    refine (Short.thetaEquiv_conj_rhoEquiv (hPair 11) _).trans ?_
    rw [conjQ_hPair_eleven, conjPermN_eleven]
  have h23 : hElt 23 * rhoEquiv (pauliQ (false, 0, 387)) * (hElt 23)⁻¹ =
      rhoEquiv (pauliQ (false, 60, 447)) := by
    refine (Short.thetaEquiv_conj_rhoEquiv (hPair 23) _).trans ?_
    rw [conjQ_hPair_twenty_three, conjXi_step]
  have h20 : hElt 20 * rhoEquiv (pauliQ (false, 60, 447)) * (hElt 20)⁻¹ =
      rhoEquiv (pauliQ (false, 3, 191)) := by
    refine (Short.thetaEquiv_conj_rhoEquiv (hPair 20) _).trans ?_
    rw [conjQ_hPair_twenty, conjYN_step]
  have hc : cConj * uStar * cConj⁻¹ =
      hElt 20 * (hElt 23 * (hElt 11 * uStar * (hElt 11)⁻¹) * (hElt 23)⁻¹) * (hElt 20)⁻¹ := by
    rw [cConj]
    group
  rw [hc, h11, h23, h20, ← qElt_one_mul_rStar_eq, qElt_mul_rStar, rhoEquiv_mul]
  rfl

theorem isConj_uBar_packetElt_one : IsConj uBar (packetElt 1) := by
  rw [isConj_iff]
  refine ⟨kappa ⟨cConj, cConj_mem_Cgen⟩, ?_⟩
  have h1 : (⟨cConj, cConj_mem_Cgen⟩ : Cgen) * uC * (⟨cConj, cConj_mem_Cgen⟩ : Cgen)⁻¹ =
      packetGen 1 * tStarC := by
    apply Subtype.ext
    show cConj * uStar * cConj⁻¹ = (packetGen 1 : SpaceB ≃ₗ[ℚ] SpaceB) * tStar
    rw [conj_uStar, coe_packetGen_of_lt (show ((1 : Fin 48) : ℕ) < 23 by decide)]
    rfl
  have hk : kappa tStarC = 1 := (kappa_eq_one_iff tStarC).2 (Or.inr rfl)
  rw [uBar, ← map_mul, ← map_inv, ← map_mul, h1, map_mul, hk, mul_one]
  rfl

end CFSG.Monster.Existence
