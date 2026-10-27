
module

public import CFSG.Monster.B.TwoA.Sp8.T9Base

public import CFSG.Monster.B.TwoA.Sp8.ElemAb
public import CFSG.Monster.B.TwoA.Sp8.QuadData
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.Lifts
public import Certificates.Certificate3060
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
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
  CFSG.Monster.B.TwoA.Census

theorem cQ_mem_T9 :
    cQ ∈ T9 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem cP_checks :
    (∀ v : Fin 8 → ZMod 2, Model.Pauli.mul (false, 0, 127) (foldP v) =
      Model.Pauli.mul (foldP v) (false, 0, 127)) ∧
    (∀ v : Fin 8 → ZMod 2, Model.Pauli.mul (false, 0, 127) (foldP v) ≠ (false, 0, 0) ∧
      Model.Pauli.mul (false, 0, 127) (foldP v) ≠ (false, 0, 191)) ∧
    (∀ v : Fin 8 → ZMod 2, (Model.Pauli.mul (false, 0, 127) (foldP v)).2.1 < 2 ^ 12 ∧
      (Model.Pauli.mul (false, 0, 127) (foldP v)).2.2 < 2 ^ 12) ∧
    Model.Pauli.mul (false, 0, 127) (false, 0, 127) = (false, 0, 0) ∧
    Model.conjYN 3 (false, 0, 127) = (false, 0, 127) :=
  Certificates.certificate3060

theorem cP_comm_PhiQ (v : Fin 8 → ZMod 2) : cP * PhiQ v = PhiQ v * cP
    := by
  rw [cP, PhiQ, ← pauliQ_mul, ← pauliQ_mul, cP_checks.1 v]

theorem cP_mul_self : cP * cP = 1 := by
  have h : pauliQ (Model.Pauli.mul (false, 0, 127) (false, 0, 127)) = cP * cP := pauliQ_mul _ _
  rw [cP_checks.2.2.2.1, show pauliQ (false, 0, 0) = 1 from pauliQ_sqPauli_one] at h
  exact h.symm

theorem cP_mem : cP ∈
    Subgroup.centralizer {rStar} := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← PhiQ_seven]
  exact cP_comm_PhiQ _

@[expose] def cC : Cgen :=
    ⟨rhoEquiv cP, rhoEquiv_mem_Cgen cP_mem⟩

theorem cQ_eq : cQ = iotaD (kappa cC)
    := by
  show iotaD (kappa ⟨rhoEquiv (rMinus 0 2), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩) = _
  rw [cC]
  exact congrArg iotaD (kappa_congr cP_eq_rMinus.symm _ _)

theorem cC_comm_PhiC
    (v : Fin 8 → ZMod 2) : cC * PhiC v = PhiC v * cC
    := by
  apply Subtype.ext
  show rhoEquiv cP * rhoEquiv (PhiQ v) = rhoEquiv (PhiQ v) * rhoEquiv cP
  rw [← rhoEquiv_mul, ← rhoEquiv_mul, cP_comm_PhiQ]

theorem cQ_comm_PhiD
    (v : Fin 8 → ZMod 2) : cQ * PhiD v = PhiD v * cQ
    := by
  have h := congrArg (fun x => iotaD (kappa x)) (cC_comm_PhiC v)
  simp only [map_mul] at h
  rw [cQ_eq, PhiD]
  exact h

theorem conjQ_slPair_cP : conjQ slPair cP = cP := by
  rw [cP, conjQ_slPair_pauliQ, cP_checks.2.2.2.2]

theorem slC_comm_cC :
    slC * cC = cC *
    slC :=
  Subtype.ext (thetaEquiv_comm_rhoEquiv conjQ_slPair_cP)

theorem ghat8_comm_cQ :
    ghat8 * cQ =
    cQ * ghat8 := by
  have h := congrArg (fun x => iotaD (kappa x)) slC_comm_cC
  simp only [map_mul] at h
  rw [ghat8_eq, cQ_eq]
  exact h

theorem cQ_comm_Psi
    (v : Fin 8 → ZMod 2) : cQ * Psi v = Psi v * cQ :=
    by
  have h1 : Commute cQ (PhiD v) := cQ_comm_PhiD v
  have h2 : Commute cQ (ghat8 ^ (v 7).val) :=
    (show Commute ghat8 cQ from ghat8_comm_cQ).symm.pow_right _
  exact (h1.mul_right h2).eq

theorem cQ_mem_centralizer_A8 :
    cQ ∈ Subgroup.centralizer
    (A8 : Set Dfull) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [← range_PsiHom] at hx
  obtain ⟨v, rfl⟩ := hx
  exact (cQ_comm_Psi v.toAdd).symm

theorem cC_mul_self : cC * cC = 1 :=
    by
  apply Subtype.ext
  show rhoEquiv cP * rhoEquiv cP = 1
  rw [← rhoEquiv_mul, cP_mul_self, rhoEquiv_one']

theorem cQ_mul_self : cQ * cQ = 1 :=
    by
  rw [cQ_eq, ← map_mul, ← map_mul, cC_mul_self, map_one, map_one]

theorem cQ_not_mem_A8 :
    cQ ∉ A8 := by
  intro h
  have hB : cQ ∈ B7 := by
    rw [← A8_inf_Ehat]
    exact ⟨h, cQ_mem_Ehat⟩
  rw [B7_eq_range] at hB
  obtain ⟨w, hw⟩ := hB
  rw [PhiDHom_apply, PhiD, cQ_eq] at hw
  have hk := iotaD_injective hw
  have h1 : kappa (PhiC w.toAdd * cC) = 1 := by
    rw [map_mul, hk, ← map_mul, cC_mul_self, map_one]
  have hb := cP_checks.2.2.1 w.toAdd
  rcases (kappa_eq_one_iff _).1 h1 with h2 | h2
  · have h3 : rhoEquiv (cP * PhiQ w.toAdd) = rhoEquiv 1 := by
      rw [rhoEquiv_mul, rhoEquiv_one']
      exact congrArg Subtype.val h2
    have h4 := rhoEquiv_injective h3
    have h5 : pauliQ (Model.Pauli.mul (false, 0, 127) (foldP w.toAdd)) = pauliQ (false, 0, 0) := by
      rw [pauliQ_mul, show pauliQ (false, 0, 0) = 1 from pauliQ_sqPauli_one]
      exact h4
    exact (cP_checks.2.1 w.toAdd).1 (pauliQ_injective_box hb ⟨by norm_num, by norm_num⟩ h5)
  · have h3 : rhoEquiv (cP * PhiQ w.toAdd) = rhoEquiv rStar := by
      rw [rhoEquiv_mul]
      exact congrArg Subtype.val h2
    have h4 := rhoEquiv_injective h3
    have h5 : pauliQ (Model.Pauli.mul (false, 0, 127) (foldP w.toAdd)) =
        pauliQ (false, 0, 191) := by
      rw [pauliQ_mul]
      rw [rStar_eq] at h4
      exact h4
    exact (cP_checks.2.1 w.toAdd).2 (pauliQ_injective_box hb ⟨by norm_num, by norm_num⟩ h5)

@[expose] def Psi9
    (v : Fin 9 → ZMod 2) : Dfull := Psi (initV v) * cQ
    ^ (v (Fin.last 8)).val

theorem cQ_pow_add (a b : ZMod 2) : cQ
    ^ (a + b).val = cQ ^ a.val *
    cQ ^ b.val := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show ((1 : ZMod 2) + 1).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero,
      pow_one, cQ_mul_self]

theorem Psi9_add
    (v w : Fin 9 → ZMod 2) : Psi9 (v + w) = Psi9 v *
    Psi9 w := by
  have hc : Commute (cQ ^ (v (Fin.last 8)).val) (Psi (initV w)) :=
    Commute.pow_left (show Commute cQ (Psi (initV w)) from cQ_comm_Psi _) _
  have hi : initV (v + w) = initV v + initV w := rfl
  rw [Psi9, Psi9, Psi9, hi, Psi_add, Pi.add_apply, cQ_pow_add, mul_assoc,
    ← mul_assoc (Psi (initV w)), ← hc.eq, mul_assoc, mul_assoc]

theorem Psi_zero' :
    Psi 0 = 1 :=
    map_one PsiHom

@[expose] def Psi9Hom :
    Multiplicative (Fin 9 → ZMod 2) →* Dfull
    where
  toFun v := Psi9 v.toAdd
  map_one' := by
    show Psi (initV 0) * cQ ^ ((0 : Fin 9 → ZMod 2) (Fin.last 8)).val = 1
    rw [show initV 0 = 0 from rfl, Psi_zero', Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
  map_mul' v w := Psi9_add v.toAdd w.toAdd

theorem Psi9Hom_apply
    (v : Multiplicative (Fin 9 → ZMod 2)) : Psi9Hom
    v = Psi9 v.toAdd := rfl

@[expose] def tT : Fin 9 → Dfull :=
  ![xhat, yhat, dhat 2 3, dhat 2 4, dhat 2 5, dhat 2 6, uhat, ghat8, cQ]

theorem tT_castSucc (j : Fin 8) : tT j.castSucc = aT j := by
  fin_cases j <;> rfl

theorem tT_last : tT (Fin.last 8) = cQ := rfl

theorem Psi9_single
    (k : Fin 9) : Psi9
    (Pi.single k 1) = tT k := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [Psi9, initV_single_last, Psi_zero', one_mul, Pi.single_eq_same,
      show (1 : ZMod 2).val = 1 from rfl, pow_one, tT_last]
  · rw [Psi9, initV_single_castSucc, Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne',
      ZMod.val_zero, pow_zero, mul_one, Psi_single, tT_castSucc]

theorem Psi9_eq_one
    (v : Fin 9 → ZMod 2) (h : Psi9 v = 1) : v = 0 :=
    by
  rcases zmod2_cases (v (Fin.last 8)) with h0 | h1
  · rw [Psi9, h0, ZMod.val_zero, pow_zero, mul_one] at h
    have hi := Psi_injective _ h
    funext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · exact h0
    · exact congrFun hi j
  · exfalso
    rw [Psi9, h1, show (1 : ZMod 2).val = 1 from rfl, pow_one] at h
    apply cQ_not_mem_A8
    rw [eq_inv_of_mul_eq_one_right h]
    exact A8.inv_mem (Psi_mem_A8 _)

theorem Psi9Hom_injective :
    Function.Injective Psi9Hom := by
  rw [injective_iff_map_eq_one]
  intro v hv
  exact congrArg Multiplicative.ofAdd (Psi9_eq_one v.toAdd hv)

theorem A8_le_T9 :
    A8 ≤ T9 := fun _ hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)

theorem Psi9_mem_T9
    (v : Fin 9 → ZMod 2) : Psi9 v ∈
    T9 :=
  T9.mul_mem (A8_le_T9 (Psi_mem_A8 _)) (T9.pow_mem cQ_mem_T9 _)

theorem Psi9_extV
    (w : Fin 8 → ZMod 2) : Psi9 (extV w) = Psi w := by
  rw [Psi9, initV_extV, extV, Fin.snoc_last, ZMod.val_zero, pow_zero, mul_one]

theorem range_Psi9Hom :
    Psi9Hom.range = T9 := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Psi9_mem_T9 v.toAdd
  · rw [T9, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact ⟨Multiplicative.ofAdd (Pi.single (Fin.last 8) 1),
        (Psi9_single (Fin.last 8)).trans tT_last⟩
    · rw [← range_PsiHom] at hx
      obtain ⟨w, rfl⟩ := hx
      exact ⟨Multiplicative.ofAdd (extV w.toAdd), Psi9_extV w.toAdd⟩

@[expose] def tEquiv :
    Multiplicative (Fin 9 → ZMod 2) ≃* T9 :=
  (MonoidHom.ofInjective Psi9Hom_injective).trans (MulEquiv.subgroupCongr range_Psi9Hom)

theorem coe_tEquiv
    (v : Multiplicative (Fin 9 → ZMod 2)) :
    (tEquiv v : Dfull) = Psi9 v.toAdd :=
  rfl

theorem tEquiv_single
    (k : Fin 9) :
    (tEquiv (Multiplicative.ofAdd (Pi.single k 1)) : Dfull) = tT k := by
  rw [coe_tEquiv, toAdd_ofAdd, Psi9_single]

theorem natCard_T9 :
    Nat.card T9 = 2 ^ 9 := by
  rw [← Nat.card_congr tEquiv.toEquiv]
  show Nat.card (Fin 9 → ZMod 2) = 2 ^ 9
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem T9_comm
    (x y : T9) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := tEquiv.surjective x
  obtain ⟨w, rfl⟩ := tEquiv.surjective y
  rw [← map_mul, ← map_mul, mul_comm]

theorem T9_sq
    (x : T9) : x ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := tEquiv.surjective x
  rw [← map_pow, show v ^ 2 = 1 from by
    rw [sq, ← ofAdd_toAdd v, ← ofAdd_add, ZModModule.add_self, ofAdd_zero], map_one]

instance isElementaryAbelian_T9 :
    CFSG.IsElementaryAbelian 2 T9 where
  is_comm := ⟨T9_comm⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one T9_sq

theorem mem_T9_iff
    (x : Dfull) : x ∈ T9 ↔ x ∈ A8 ∨ cQ * x ∈ A8 := by
  constructor
  · intro hx
    rw [← range_Psi9Hom] at hx
    obtain ⟨v, rfl⟩ := hx
    rw [Psi9Hom_apply]
    rcases zmod2_cases (v.toAdd (Fin.last 8)) with h0 | h1
    · left
      rw [Psi9, h0, ZMod.val_zero, pow_zero, mul_one]
      exact Psi_mem_A8 _
    · right
      rw [Psi9, h1, show (1 : ZMod 2).val = 1 from rfl, pow_one, ← cQ_comm_Psi, ← mul_assoc,
        cQ_mul_self, one_mul]
      exact Psi_mem_A8 _
  · rintro (h | h)
    · exact A8_le_T9 h
    · have e : x = cQ * (cQ * x) := by rw [← mul_assoc, cQ_mul_self, one_mul]
      rw [e]
      exact T9.mul_mem cQ_mem_T9 (A8_le_T9 h)

end CFSG.Monster.B.TwoA.Sp8
