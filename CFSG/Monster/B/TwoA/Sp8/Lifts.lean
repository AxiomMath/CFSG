
module

public import CFSG.Monster.B.TwoA.Sp8.LiftsBase

public import CFSG.Monster.B.TwoA.Sp8.Data
public import CFSG.Monster.B.TwoA.Census.CentralSqrt
public meta import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import Certificates.Certificate3057
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census

theorem foldP_checks :
    (∀ v w : Fin 8 → ZMod 2, foldP (v + w) = Model.Pauli.mul (foldP v) (foldP w)) ∧
    (∀ k : Fin 8, foldP (Pi.single k 1) = liftP k) ∧
    (∀ v : Fin 8 → ZMod 2, foldP v = (false, 0, 0) → v = 0) ∧
    (∀ v : Fin 8 → ZMod 2, foldP v = (false, 0, 191) → v = Pi.single 7 1) ∧
    (∀ v : Fin 8 → ZMod 2, (foldP v).2.1 < 2 ^ 12 ∧ (foldP v).2.2 < 2 ^ 12) ∧
    (∀ v : Fin 8 → ZMod 2, Model.conjYN 3 (foldP v) = foldP v) :=
  Certificates.certificate3057

theorem PhiQ_add (v w : Fin 8 → ZMod 2) : PhiQ (v + w) = PhiQ v *
    PhiQ w := by
  rw [PhiQ, foldP_checks.1, pauliQ_mul]
  rfl

theorem PhiQ_comm (v w : Fin 8 → ZMod 2) : PhiQ v * PhiQ w = PhiQ w *
    PhiQ v := by
  rw [← PhiQ_add, ← PhiQ_add, add_comm]

theorem PhiQ_single (k : Fin 8) : PhiQ (Pi.single k 1) = pauliQ
    (liftP k) := by
  rw [PhiQ, foldP_checks.2.1]

theorem PhiQ_seven : PhiQ (Pi.single 7 1) = rStar := by
  rw [PhiQ_single, rStar_eq]
  rfl

theorem PhiQ_mem (v : Fin 8 → ZMod 2) : PhiQ v ∈ Subgroup.centralizer
    {rStar} := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← PhiQ_seven]
  exact PhiQ_comm _ _

theorem PhiQ_eq_one_iff (v : Fin 8 → ZMod 2) : PhiQ v = 1 ↔ v = 0 :=
    by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 : pauliQ (foldP v) = pauliQ (false, 0, 0) := by
      rw [show pauliQ (false, 0, 0) = 1 from pauliQ_sqPauli_one]
      exact h
    exact foldP_checks.2.2.1 v (pauliQ_injective_box (foldP_checks.2.2.2.2.1 v)
      ⟨by norm_num, by norm_num⟩ h0)
  · subst h
    have h0 : PhiQ 0 * PhiQ 0 = PhiQ 0 * 1 := by rw [← PhiQ_add, add_zero, mul_one]
    exact mul_left_cancel h0

theorem PhiQ_eq_rStar_iff (v : Fin 8 → ZMod 2) : PhiQ v = rStar ↔ v =
    Pi.single 7 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ PhiQ_seven⟩
  have h0 : pauliQ (foldP v) = pauliQ (false, 0, 191) := by
    rw [rStar_eq] at h
    exact h
  exact foldP_checks.2.2.2.1 v (pauliQ_injective_box (foldP_checks.2.2.2.2.1 v)
    ⟨by norm_num, by norm_num⟩ h0)

@[expose] def PhiC (v : Fin 8 → ZMod 2) : Cgen :=
  ⟨rhoEquiv (PhiQ v), rhoEquiv_mem_Cgen (PhiQ_mem v)⟩

@[expose] def PhiD (v : Fin 8 → ZMod 2) : Dfull := iotaD
    (kappa (PhiC v))

theorem rhoEquiv_PhiQ_add (v w : Fin 8 → ZMod 2) :
    rhoEquiv (PhiQ (v + w)) = rhoEquiv (PhiQ v) * rhoEquiv (PhiQ w) := by
  rw [PhiQ_add, PhiQ_comm, rhoEquiv_mul]

theorem PhiC_add (v w : Fin 8 → ZMod 2) : PhiC (v + w) = PhiC v *
    PhiC w :=
  Subtype.ext (rhoEquiv_PhiQ_add v w)

theorem PhiD_add (v w : Fin 8 → ZMod 2) : PhiD (v + w) = PhiD v *
    PhiD w := by
  rw [PhiD, PhiC_add, map_mul, map_mul]
  rfl

theorem PhiD_comm (v w : Fin 8 → ZMod 2) : PhiD v * PhiD w = PhiD w *
    PhiD v := by
  rw [← PhiD_add, ← PhiD_add, add_comm]

theorem PhiD_zero : PhiD 0 = 1 := by
  have h : PhiD 0 * PhiD 0 = PhiD 0 * 1 := by rw [← PhiD_add, add_zero, mul_one]
  exact mul_left_cancel h

theorem PhiD_mul_self (v : Fin 8 → ZMod 2) : PhiD v * PhiD v = 1 :=
    by
  rw [← PhiD_add, ZModModule.add_self, PhiD_zero]

theorem PhiC_eq_tStarC_iff (v : Fin 8 → ZMod 2) : PhiC v = tStarC ↔ v
    = Pi.single 7 1 := by
  rw [← PhiQ_eq_rStar_iff]
  constructor
  · intro h
    exact rhoEquiv_injective (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (congrArg rhoEquiv h)

theorem PhiC_eq_one_iff (v : Fin 8 → ZMod 2) : PhiC v = 1 ↔ v = 0 :=
    by
  rw [← PhiQ_eq_one_iff]
  constructor
  · intro h
    have h' : rhoEquiv (PhiQ v) = rhoEquiv 1 := by
      rw [rhoEquiv_one']
      exact congrArg Subtype.val h
    exact rhoEquiv_injective h'
  · intro h
    apply Subtype.ext
    show rhoEquiv (PhiQ v) = 1
    rw [h, rhoEquiv_one']

theorem PhiD_eq_one_iff (v : Fin 8 → ZMod 2) : PhiD v = 1 ↔ v = 0 ∨ v
    = Pi.single 7 1 := by
  rw [PhiD, ← map_one iotaD, iotaD_injective.eq_iff, kappa_eq_one_iff, PhiC_eq_one_iff,
    PhiC_eq_tStarC_iff]

theorem PhiD_seven : PhiD (Pi.single 7 1) = 1 :=
    (PhiD_eq_one_iff _).2 (Or.inr rfl)

theorem PhiD_single_zero : PhiD (Pi.single 0 1) = xhat := by
  have h : PhiC (Pi.single 0 1) = xC := Subtype.ext (by
    show rhoEquiv (PhiQ (Pi.single 0 1)) = xmat
    rw [PhiQ_single, xmat]
    exact congrArg rhoEquiv pauliQ_z)
  show iotaD (kappa (PhiC (Pi.single 0 1))) = piD (inclGen xC)
  rw [h, iotaD_kappa]

theorem PhiD_single_one :
    PhiD (Pi.single 1 1) =
    yhat := by
  have h : PhiC (Pi.single 1 1) = ⟨rhoEquiv wQ, rhoEquiv_mem_Cgen wQ_mem_centralizer⟩ :=
    Subtype.ext (by
      show rhoEquiv (PhiQ (Pi.single 1 1)) = rhoEquiv wQ
      rw [PhiQ_single]
      exact congrArg rhoEquiv pauliQ_omega)
  show iotaD (kappa (PhiC (Pi.single 1 1))) = iotaD zbar
  rw [h, zbar_eq]

theorem PhiD_single_cocode {k : Fin 8} {i j : Fin 24} {w D : ℕ}
    (hk : liftP k = (false, 0, D))
    (hb : bvec 24 w = Pi.single i 1 + Pi.single j 1) (h : Model.dualN w = D) :
    PhiD (Pi.single k 1) = dhat i j := by
  have hc : PhiC (Pi.single k 1) =
      ⟨rhoEquiv (rMinus i j), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩ :=
    Subtype.ext (by
      show rhoEquiv (PhiQ (Pi.single k 1)) = rhoEquiv (rMinus i j)
      rw [PhiQ_single, hk]
      exact congrArg rhoEquiv (pauliQ_cocode hb h))
  show iotaD (kappa (PhiC (Pi.single k 1))) = iotaD (dbar i j)
  rw [hc]
  rfl

theorem PhiD_single_two : PhiD (Pi.single 2 1) = dhat 2 3 :=
  PhiD_single_cocode (w := 12) rfl (by decide) (by decide)

theorem PhiD_single_three : PhiD (Pi.single 3 1) = dhat 2 4 :=
  PhiD_single_cocode (w := 20) rfl (by decide) (by decide)

theorem PhiD_single_four : PhiD (Pi.single 4 1) = dhat 2 5 :=
  PhiD_single_cocode (w := 36) rfl (by decide) (by decide)

theorem PhiD_single_five : PhiD (Pi.single 5 1) = dhat 2 6 :=
  PhiD_single_cocode (w := 68) rfl (by decide) (by decide)

theorem PhiD_single_six :
    PhiD (Pi.single 6 1) = uhat := by
  have h : PhiC (Pi.single 6 1) =
      ⟨rhoEquiv (XQ ⟨dC, 0⟩), rhoEquiv_mem_Cgen XQ_dC_mem_centralizer⟩ :=
    Subtype.ext (by
      show rhoEquiv (PhiQ (Pi.single 6 1)) = rhoEquiv (XQ ⟨dC, 0⟩)
      rw [PhiQ_single]
      exact congrArg rhoEquiv pauliQ_X)
  show iotaD (kappa (PhiC (Pi.single 6 1))) = iotaD ubar
  rw [h]
  rfl

theorem PhiD_single
    {k : Fin 8} (hk : (k : ℕ) < 7) :
    PhiD
    (Pi.single k 1) = aT k := by
  fin_cases k
  · exact PhiD_single_zero
  · exact PhiD_single_one
  · exact PhiD_single_two
  · exact PhiD_single_three
  · exact PhiD_single_four
  · exact PhiD_single_five
  · exact PhiD_single_six
  · exact absurd hk (by decide)

end CFSG.Monster.B.TwoA.Sp8
