
module

public import CFSG.Monster.B.Rep4371.SmallFaithfulBase
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot CFSG.Monster.B.Rep4371
open scoped Matrix

noncomputable def ePauli (i : Fin 23) : Cbar :=
  kappa ⟨rhoEquiv (qElt i), rhoEquiv_qElt_mem_Cgen i⟩

theorem ePauli_mem_Ebar (i : Fin 23) : ePauli i ∈ Ebar := kappa_rho_mem_Ebar (qElt_mem_centralizer i)

theorem packetElt_pauli (i : Fin 23) : packetElt ⟨i, by omega⟩ = ePauli i :=
  congrArg kappa (Subtype.ext (coe_packetGen_of_lt (k := ⟨i, by omega⟩) i.2))

theorem ePauli_zero : ePauli 0 = xbar := by
  rw [ePauli]
  exact (kappa_rho_eq_xbar_iff _).2 (Or.inl (by simp [qElt]))

theorem coordOf_qElt_T (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 11) :
    coordOf (qElt ⟨i, by omega⟩) = (basisC ⟨i, by omega⟩ + epsStar i • basisC 0, 0) := by
  rw [qElt, ite_eq_right (show ¬ ((⟨i, by omega⟩ : Fin 23) : ℕ) = 0 by simp; omega),
    dite_eq_left (show ((⟨i, by omega⟩ : Fin 23) : ℕ) ≤ 11 from h2), TQ,
    Griess.coordOf_spinEquiv]

theorem coordOf_qElt_D (i : ℕ) (h1 : 12 ≤ i) (h2 : i ≤ 22) :
    coordOf (qElt ⟨i, by omega⟩) = (0, deltaBasis ⟨i - 11, by omega⟩) := by
  rw [qElt, ite_eq_right (show ¬ ((⟨i, by omega⟩ : Fin 23) : ℕ) = 0 by simp; omega),
    dite_eq_right (show ¬ ((⟨i, by omega⟩ : Fin 23) : ℕ) ≤ 11 by simp; omega), coordOf_DQ]

theorem pair_qT_delta {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ 11) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 11) :
    pair (basisC ⟨i, by omega⟩ + epsStar i • basisC 0) (deltaBasis ⟨j, by omega⟩) =
      if i = j then 1 else 0 := by
  rw [pair_add_left, pair_smul_left, pair_deltaBasis, pair_deltaBasis]
  have h0 : (0 : Fin 12) ≠ ⟨j, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  rw [ite_eq_right h0, mul_zero, add_zero]
  by_cases h : i = j
  · rw [ite_eq_left (Fin.ext h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h (congrArg Fin.val e)), ite_eq_right h]

theorem bL_pauli (k l : Fin 22) :
    QuadraticMap.polarBilin qL (phi0 (coordOf (qElt ⟨k + 1, by omega⟩)))
      (phi0 (coordOf (qElt ⟨l + 1, by omega⟩))) = gramPauli k l := by
  rw [gramPauli, Matrix.of_apply]
  have hk22 := k.isLt
  have hl22 := l.isLt
  by_cases hk : (k : ℕ) < 11 <;> by_cases hl : (l : ℕ) < 11
  · rw [coordOf_qElt_T (k + 1) (by omega) (by omega), coordOf_qElt_T (l + 1) (by omega) (by omega),
      bL_phi0, pair_zero_right, pair_zero_right, add_zero, ite_eq_right (by omega)]
  · rw [coordOf_qElt_T (k + 1) (by omega) (by omega), coordOf_qElt_D (l + 1) (by omega) (by omega),
      bL_phi0, pair_zero_left, add_zero,
      pair_qT_delta (i := k + 1) (j := l + 1 - 11) (by omega) (by omega) (by omega) (by omega)]
    by_cases h : (k : ℕ) + 11 = l
    · rw [ite_eq_left (by omega), ite_eq_left (Or.inl h)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [coordOf_qElt_D (k + 1) (by omega) (by omega), coordOf_qElt_T (l + 1) (by omega) (by omega),
      bL_phi0, pair_zero_left, zero_add,
      pair_qT_delta (i := l + 1) (j := k + 1 - 11) (by omega) (by omega) (by omega) (by omega)]
    by_cases h : (l : ℕ) + 11 = k
    · rw [ite_eq_left (by omega), ite_eq_left (Or.inr h)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [coordOf_qElt_D (k + 1) (by omega) (by omega), coordOf_qElt_D (l + 1) (by omega) (by omega),
      bL_phi0, pair_zero_left, pair_zero_left, add_zero, ite_eq_right (by omega)]

noncomputable def ePauli' (k : Fin 22) : Cbar := ePauli ⟨k + 1, by omega⟩

theorem ePauli'_mem_Ebar (k : Fin 22) : ePauli' k ∈ Ebar := ePauli_mem_Ebar _

theorem ePauli'_rel (k l : Fin 22) :
    ePauli' k * ePauli' l = ePauli' l * ePauli' k * xbar ^ (gramPauli k l).val := by
  rw [← bL_pauli]
  exact kappa_rho_mul_eq (qElt_mem_centralizer _) (qElt_mem_centralizer _)

theorem packetElt_mem_Jbar {k : ℕ} (hk : k < 47) : packetElt ⟨k, by omega⟩ ∈ Jbar := by
  by_cases h : k < 23
  · rw [packetElt_pauli ⟨k, h⟩]
    exact Ebar_le_Jbar (ePauli_mem_Ebar _)
  · have he : (⟨k, by omega⟩ : Fin 48) = ⟨23 + (k - 23 : ℕ), by omega⟩ := Fin.ext (by simp; omega)
    rw [he, packetElt_h ⟨k - 23, by omega⟩]
    exact kappa_mem_Jbar (hElt_mem_Jstar _)

theorem coe_chiMat (s : Cbar) :
    ((chiMat s : GL (Fin 4371) ℚ) : Matrix (Fin 4371) (Fin 4371) ℚ) =
      LinearMap.toMatrix Rbasis Rbasis (chi s : Vst →ₗ[ℚ] Vst) := rfl

theorem coe_chiMat_packetElt
    (k : Fin 48) :
    ((chiMat (packetElt k) : GL (Fin 4371) ℚ) : Matrix (Fin 4371) (Fin 4371) ℚ) = (packetN k)ᵀ := by
  rw [coe_chiMat, toMatrix_chi_packetElt]

end CFSG.Monster.B
