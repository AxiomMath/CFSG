
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsBase

public import CFSG.Monster.B.TwoA.Sp8.ElemAb
public import CFSG.Monster.B.TwoA.Sp8.GenActionData
public import CFSG.Monster.B.Gen.HRecords
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionData
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Sp8.Lifts
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import Certificates.Certificate3072
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
  CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

@[expose] def h1Lift (k : Fin 44) : Pvis :=
  if (k : ℕ) < 23 then rhoPair (pauliQ (pauliGen k))
  else if h : (k : ℕ) < 32 then gPair (fAut ⟨k - 23, by omega⟩)
  else if (k : ℕ) < 43 then signProd (signCodesOf (k - 32))
  else xiSignPair

theorem h1Lift_pauli {k : Fin 44} (h : (k : ℕ) < 23) :
    h1Lift k = rhoPair (pauliQ (pauliGen k)) :=
  ite_eq_left h

theorem h1Lift_perm {k : Fin 44} (h1 : 23 ≤ (k : ℕ))
    (h2 : (k : ℕ) < 32) :
    h1Lift k = gPair (fAut ⟨k - 23, by omega⟩) := by
  rw [h1Lift, ite_eq_right (by omega), dite_eq_left h2]

theorem h1Lift_sign {k : Fin 44} (h1 : 32 ≤ (k : ℕ))
    (h2 : (k : ℕ) < 43) :
    h1Lift k = signProd (signCodesOf (k - 32)) := by
  rw [h1Lift, ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left h2]

theorem h1Lift_xi {k : Fin 44} (h : 43 ≤ (k : ℕ)) :
    h1Lift k = xiSignPair := by
  rw [h1Lift, ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega)]

theorem repPerm_fAut (j : Fin 9) :
    RepPerm (fAut j : Equiv.Perm (Fin 24)) fPerms[(j : ℕ)]! :=
  fun i => fAut_apply j i

theorem epsP_fAut (j : Fin 9) :
    epsP (fAut j) = boolZ (Model.kappaN fPerms[(j : ℕ)]! 63) := by
  rw [epsP, ΩC_eq_toC, kappaP_toC (fAut j) (repPerm_fAut j) 63]

theorem DQ_epsP (j : Fin 9) :
    DQ (epsP (fAut j) • e0Cls) = pauliQ (false, 0, epsDual j) := by
  rw [epsP_fAut, e0Cls_eq, ← toD_ite, pauliQ_D]
  rfl

theorem gPair_fAut (j : Fin 9) :
    gPair (fAut j) = TwoA.permPair (fAut j) * rhoPair (pauliQ (false, 0, epsDual j)) := by
  rw [gPair, DQ_epsP]

theorem conjQ_h1Lift (k : Fin 44) (y : Model.Pauli) :
    conjQ (h1Lift k) (pauliQ y) = pauliQ (h1ConjN k y) := by
  by_cases h1 : (k : ℕ) < 23
  · refine (conjQ_congr (h1Lift_pauli h1) _).trans ((conjQ_rhoPair_toQ _ y).trans ?_)
    exact congrArg pauliQ (h1ConjN_pauli h1 y).symm
  by_cases h2 : (k : ℕ) < 32
  · have hp := repPerm_fAut ⟨k - 23, by omega⟩
    refine (conjQ_congr ((h1Lift_perm (by omega) h2).trans (gPair_fAut _)) _).trans ?_
    refine (conjQ_mul _ _ _).trans ?_
    refine (congrArg _ (conjQ_perm_toQ _ hp y)).trans ((conjQ_rhoPair_toQ _ _).trans ?_)
    exact congrArg pauliQ (h1ConjN_perm (by omega) h2 y).symm
  by_cases h3 : (k : ℕ) < 43
  · refine (conjQ_congr (h1Lift_sign (by omega) h3) _).trans ((conjQ_signProd _ y).trans ?_)
    exact congrArg pauliQ (h1ConjN_sign (by omega) h3 y).symm
  · refine (conjQ_congr (h1Lift_xi (by omega)) _).trans ?_
    refine (conjQ_mul _ _ _).trans ?_
    refine (congrArg _ (conjQ_xi_toQ y)).trans ((conjQ_sign_toQ 1 _).trans ?_)
    exact congrArg pauliQ (h1ConjN_xi (by omega) y).symm

theorem h1ConjN_rStar :
    ∀ k < 44, h1ConjN k (false, 0, 191) = (false, 0, 191) :=
  Certificates.certificate3072

theorem conjQ_h1Lift_rStar
    (k : Fin 44) : conjQ (h1Lift k) rStar =
    rStar := by
  rw [B.rStar_eq, conjQ_h1Lift, h1ConjN_rStar k k.2]

theorem h1Lift_mem_Jstar (k : Fin 44)
    : thetaEquiv (h1Lift k) ∈ Jstar
    := by
  refine ⟨thetaEquiv_mem_Gvis _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h := Short.thetaEquiv_conj_rhoEquiv (h1Lift k) rStar
  rw [conjQ_h1Lift_rStar, mul_inv_eq_iff_eq_mul] at h
  exact h

@[expose] def h1LiftC (k : Fin 44) :
    Cgen :=
  ⟨thetaEquiv (h1Lift k), Jstar_le_Cgen (h1Lift_mem_Jstar k)⟩

@[expose] def h1LiftD (k : Fin 44) :
    Dfull := iotaD
    (kappa (h1LiftC k))

theorem h1LiftD_mem_Jhat (k : Fin 44)
    : h1LiftD k ∈ Jhat := by
  rw [Jhat_eq_map]
  exact ⟨kappa (h1LiftC k), kappa_mem_Jbar (h1Lift_mem_Jstar k), rfl⟩

theorem mk_gPair
    (j : Fin 9) :
    (QuotientGroup.mk ((gPair (fAut j) : Pvis) : GL SpinIdx ℚ × latticeO).2 : OLq) =
      (cGen ⟨j, by omega⟩ : OLq) := by
  rw [cGen_of_lt (show ((⟨j, by omega⟩ : Fin 21) : ℕ) < 9 from j.2), gPair, Subgroup.coe_mul,
    Prod.snd_mul, coe_rhoPair, mul_one]
  rfl

theorem jhatToKv0_h1LiftD
    {k : Fin 44} (hk : 23 ≤ (k : ℕ))
    :
    jhatToKv0 ⟨h1LiftD k, h1LiftD_mem_Jhat k⟩ = (cGen ⟨k - 23, by omega⟩)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv]
  refine (coe_jhatToKv0_pair (h1Lift_mem_Jstar k) (h1LiftD_mem_Jhat k)).trans (congrArg _ ?_)
  by_cases h2 : (k : ℕ) < 32
  · have e := h1Lift_perm hk h2
    simp only [e]
    exact mk_gPair ⟨k - 23, by omega⟩
  by_cases h3 : (k : ℕ) < 43
  · have e := h1Lift_sign (by omega) h3
    simp only [e]
    rw [mk_signProd (k - 32) (by omega), cGen_of_ge (show 9 ≤ ((⟨k - 23, by omega⟩ : Fin 21) : ℕ)
      by simp; omega)]
    congr 2
    simp
    omega
  · have e := h1Lift_xi (k := k) (by omega)
    have hk43 : (k : ℕ) = 43 := by omega
    simp only [e]
    rw [← hPair_xi, mk_hPair_snd, cGen_of_ge (show 9 ≤ ((⟨k - 23, by omega⟩ : Fin 21) : ℕ)
      by simp; omega)]
    congr 2
    simp [hk43]

theorem h1LiftC_pauli {k : Fin 44}
    (h : (k : ℕ) < 23) :
    h1LiftC k = ⟨rhoEquiv (pauliQ (pauliGen k)), rhoEquiv_mem_Cgen (pauliQ_pauliGen_mem k h)⟩ :=
  Subtype.ext (congrArg thetaEquiv (h1Lift_pauli h))

theorem h1LiftD_mem_Ehat {k : Fin 44}
    (h : (k : ℕ) < 23) : h1LiftD k
    ∈ Ehat := by
  rw [h1LiftD, h1LiftC_pauli h]
  exact ⟨_, kappa_rho_mem_Ebar (pauliQ_pauliGen_mem k h), rfl⟩

theorem h1LiftD_mem_H1
    (k : Fin 44) : h1LiftD k ∈
    H1 := by
  refine (mem_H1_iff _).2 ⟨h1LiftD_mem_Jhat k, ?_⟩
  by_cases h : (k : ℕ) < 23
  · rw [jhatToKv0_eq_one_of_mem_Ehat _ (h1LiftD_mem_Ehat h)]
    exact Cr.one_mem
  · rw [jhatToKv0_h1LiftD (by omega)]
    exact Cr.inv_mem (cGen_mem_Cr _)

end CFSG.Monster.B.TwoA.Sp8
