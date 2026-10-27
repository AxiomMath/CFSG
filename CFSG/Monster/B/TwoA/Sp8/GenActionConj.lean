
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionDiff
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionDiff
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import Certificates.Certificate3074
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

theorem h1LiftC_conj_PhiC
    (k : Fin 44)
    {v w : Fin 8 → ZMod 2}
    (h : h1ConjN k (foldP v) = foldP w) : h1LiftC k * PhiC v * (h1LiftC k)⁻¹ = PhiC w := by
  apply Subtype.ext
  show thetaEquiv (h1Lift k) * rhoEquiv (PhiQ v) * (thetaEquiv (h1Lift k))⁻¹ = rhoEquiv (PhiQ w)
  rw [Short.thetaEquiv_conj_rhoEquiv]
  exact congrArg rhoEquiv ((conjQ_h1Lift k (foldP v)).trans (congrArg pauliQ h))

theorem h1LiftD_conj_PhiD
    (k : Fin 44)
    {v w : Fin 8 → ZMod 2}
    (h : h1ConjN k (foldP v) = foldP w) : h1LiftD k * PhiD v * (h1LiftD k)⁻¹ = PhiD w := by
  rw [h1LiftD, PhiD, PhiD, conj_iotaD_kappa, h1LiftC_conj_PhiC k h]

theorem PhiD_add_seven (v : Fin 8 → ZMod 2) : PhiD
    (v + Pi.single 7 1) = PhiD v := by
  rw [PhiD_add, PhiD_seven, mul_one]

theorem liftRowCheck : ∀ k : Fin 44, ∀ j : Fin 7, genRow k j < 128 ∧
    (h1ConjN k (liftP j.castSucc) = foldP (bvec 8 (genRow k j)) ∨
      h1ConjN k (liftP j.castSucc) = foldP (bvec 8 (genRow k j) + Pi.single 7 1)) :=
  Certificates.certificate3074.1

theorem liftDiffCheck :
    ∀ k : Fin 44, 128 ≤ genRow k 7 ∧ genRow k 7 < 256 ∧
    (gDiff k = foldP (bvec 8 (genRow k 7)) ∨
      gDiff k = foldP (bvec 8 (genRow k 7) + Pi.single 7 1)) :=
  Certificates.certificate3074.2

theorem rhoEquiv_gDiff_mem
    (k : Fin 44) :
    pauliQ (gDiff k) ∈ Subgroup.centralizer {rStar} := by
  rcases (liftDiffCheck k).2.2 with h | h
  · rw [h]
    exact PhiQ_mem _
  · rw [h]
    exact PhiQ_mem _

@[expose] def gDiffC (k : Fin 44) :
    Cgen :=
  ⟨rhoEquiv (pauliQ (gDiff k)), rhoEquiv_mem_Cgen (rhoEquiv_gDiff_mem k)⟩

theorem h1LiftC_mul_slC
    (k : Fin 44) : h1LiftC k * slC = slC *
    (gDiffC k * h1LiftC k) := by
  apply Subtype.ext
  show thetaEquiv (h1Lift k) * thetaEquiv slPair =
    thetaEquiv slPair * (thetaEquiv (rhoPair (pauliQ (gDiff k))) * thetaEquiv (h1Lift k))
  rw [← thetaEquiv_mul, slPair_mul_h1Lift, thetaEquiv_mul, thetaEquiv_mul]

theorem iotaD_kappa_gDiffC
    (k : Fin 44) :
    iotaD (kappa (gDiffC k)) = PhiD (bvec 8 (genRow k 7)) := by
  rcases (liftDiffCheck k).2.2 with h | h
  · have e : gDiffC k = PhiC (bvec 8 (genRow k 7)) :=
      Subtype.ext (congrArg rhoEquiv (congrArg pauliQ h))
    rw [e]
    rfl
  · have e : gDiffC k = PhiC (bvec 8 (genRow k 7) + Pi.single 7 1) :=
      Subtype.ext (congrArg rhoEquiv (congrArg pauliQ h))
    rw [e, ← PhiD_add_seven (bvec 8 (genRow k 7))]
    rfl

theorem h1LiftD_conj_ghat8
    (k : Fin 44) :
    h1LiftD k * ghat8 * (h1LiftD k)⁻¹ = PhiD (bvec 8 (genRow k 7)) * ghat8 := by
  have h := congrArg (fun x => iotaD (kappa x)) (h1LiftC_mul_slC k)
  simp only [map_mul] at h
  rw [← ghat8_eq, iotaD_kappa_gDiffC] at h
  have h' : h1LiftD k * ghat8 = ghat8 * (PhiD (bvec 8 (genRow k 7)) * h1LiftD k) := h
  rw [h', mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ghat8_comm_PhiD]

theorem aEquiv_bvec_lt
    {r : ℕ}
    (hr : r < 128) :
    (aEquiv (Multiplicative.ofAdd (bvec 8 r)) : Dfull) = PhiD (bvec 8 r) := by
  rw [coe_aEquiv, toAdd_ofAdd, Psi, bvec_seven_eq_zero hr, ZMod.val_zero, pow_zero, mul_one]

theorem aEquiv_bvec_ge
    {r : ℕ}
    (h1 : 128 ≤ r) (h2 : r < 256) :
    (aEquiv (Multiplicative.ofAdd (bvec 8 r)) : Dfull) = PhiD (bvec 8 r) * ghat8 := by
  rw [coe_aEquiv, toAdd_ofAdd, Psi, bvec_seven_eq_one h1 h2, show (1 : ZMod 2).val = 1 from rfl,
    pow_one]

theorem h1LiftD_conj_aT
    (k : Fin 44) (j : Fin 8) :
    h1LiftD k * aT j * (h1LiftD k)⁻¹ =
      (aEquiv (Multiplicative.ofAdd (bvec 8 (genRow k j))) : Dfull) := by
  by_cases hj : (j : ℕ) < 7
  · obtain ⟨hr, hc⟩ := liftRowCheck k ⟨j, hj⟩
    have hjj : (⟨j, hj⟩ : Fin 7).castSucc = j := Fin.ext rfl
    rw [hjj] at hc
    rw [aEquiv_bvec_lt hr, ← PhiD_single hj]
    have hf : foldP (Pi.single j 1) = liftP j := foldP_checks.2.1 j
    rcases hc with h | h
    · exact h1LiftD_conj_PhiD k (hf.symm ▸ h)
    · rw [h1LiftD_conj_PhiD k (hf.symm ▸ h), PhiD_add_seven]
  · have hj7 : j = 7 := by
      ext
      show (j : ℕ) = 7
      have := j.2
      omega
    subst hj7
    obtain ⟨h1, h2, -⟩ := liftDiffCheck k
    show h1LiftD k * aT 7 * (h1LiftD k)⁻¹ =
      (aEquiv (Multiplicative.ofAdd (bvec 8 (genRow k 7))) : Dfull)
    rw [aEquiv_bvec_ge h1 h2]
    exact h1LiftD_conj_ghat8 k

theorem tauhat_conj_genRow
    (j : Fin 8)
    :
    tauhat * aT j * tauhat⁻¹ = (aEquiv (Multiplicative.ofAdd (bvec 8 (genRow 44 j))) : Dfull) := by
  rw [genRow_tri, tauhat_conj_aT]

end CFSG.Monster.B.TwoA.Sp8
