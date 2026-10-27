
module

public import CFSG.Monster.B.TwoA.Sp8.A8Base

public import CFSG.Monster.B.TwoA.Sp8.Lifts
public import CFSG.Monster.Visible.SignCompat.Triality
public meta import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import Certificates.Certificate3058
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
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
  CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.B.Co2

@[expose] def PhiDHom : Multiplicative (Fin 8 → ZMod 2) →* Dfull
    where
  toFun v := PhiD v.toAdd
  map_one' := PhiD_zero
  map_mul' v w := PhiD_add v.toAdd w.toAdd

theorem PhiDHom_apply (v : Multiplicative (Fin 8 → ZMod 2)) : PhiDHom
    v = PhiD v.toAdd := rfl

theorem gen_mem_B7 {x : Dfull}
    (hx : x ∈ ({xhat, yhat, dhat 2 3, dhat 2 4, dhat 2 5, dhat 2 6, uhat} : Set Dfull)) :
    x ∈ B7 :=
  Subgroup.subset_closure hx

theorem PhiD_single_mem_B7
    (k : Fin 8) : PhiD (Pi.single k 1)
    ∈ B7 :=
    by
  fin_cases k
  · show PhiD (Pi.single 0 1) ∈ B7
    rw [PhiD_single_zero]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 1 1) ∈ B7
    rw [PhiD_single_one]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 2 1) ∈ B7
    rw [PhiD_single_two]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 3 1) ∈ B7
    rw [PhiD_single_three]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 4 1) ∈ B7
    rw [PhiD_single_four]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 5 1) ∈ B7
    rw [PhiD_single_five]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 6 1) ∈ B7
    rw [PhiD_single_six]
    exact gen_mem_B7 (by simp)
  · show PhiD (Pi.single 7 1) ∈ B7
    rw [PhiD_seven]
    exact B7.one_mem

theorem PhiD_mem_B7
    (v : Fin 8 → ZMod 2) : PhiD v ∈
    B7 := by
  have hv : v = ∑ k : Fin 8, Pi.single k (v k) := (Finset.univ_sum_single v).symm
  rw [hv]
  refine Finset.sum_induction _ (fun w => PhiD w ∈ B7) (fun a b ha hb => ?_) ?_ fun k _ => ?_
  · rw [PhiD_add]
    exact B7.mul_mem ha hb
  · rw [PhiD_zero]
    exact B7.one_mem
  · rcases zmod2_cases (v k) with h0 | h1
    · rw [h0, Pi.single_zero, PhiD_zero]
      exact B7.one_mem
    · rw [h1]
      exact PhiD_single_mem_B7 k

theorem B7_eq_range :
    B7 = PhiDHom.range := by
  apply le_antisymm
  · rw [B7, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd (Pi.single 0 1), PhiD_single_zero⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 1 1), PhiD_single_one⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 2 1), PhiD_single_two⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 3 1), PhiD_single_three⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 4 1), PhiD_single_four⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 5 1), PhiD_single_five⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 6 1), PhiD_single_six⟩
  · rintro _ ⟨v, rfl⟩
    exact PhiD_mem_B7 v.toAdd

theorem conjQ_slPair_PhiQ (v : Fin 8 → ZMod 2) : conjQ slPair
    (PhiQ v) = PhiQ v := by
  rw [PhiQ, conjQ_slPair_pauliQ, foldP_checks.2.2.2.2.2 v]

theorem thetaEquiv_slPair_mem_Cgen : thetaEquiv slPair ∈ Cgen := by
  rw [thetaEquiv_slPair]
  exact Cgen.mul_mem (Cgen.mul_mem tauB_mem_Cgen (rhoEquiv_mem_Cgen XQ_dC_mem_centralizer))
    (Cgen.inv_mem tauB_mem_Cgen)

@[expose] def slC :
    Cgen := ⟨thetaEquiv slPair, thetaEquiv_slPair_mem_Cgen⟩

theorem slC_eq :
    slC = tauC * ⟨rhoEquiv (XQ ⟨dC, 0⟩), rhoEquiv_mem_Cgen XQ_dC_mem_centralizer⟩ *
    tauC⁻¹ :=
  Subtype.ext thetaEquiv_slPair

theorem ghat8_eq : ghat8 = iotaD (kappa slC) := by
  rw [slC_eq]
  simp only [map_mul, map_inv]
  rfl

theorem slC_comm_PhiC
    (v : Fin 8 → ZMod 2) : slC * PhiC v = PhiC v *
    slC :=
  Subtype.ext (thetaEquiv_comm_rhoEquiv (conjQ_slPair_PhiQ v))

theorem ghat8_comm_PhiD
    (v : Fin 8 → ZMod 2) : ghat8 * PhiD v = PhiD
    v * ghat8 := by
  have h := congrArg (fun x => iotaD (kappa x)) (slC_comm_PhiC v)
  simp only [map_mul] at h
  rw [ghat8_eq, PhiD]
  exact h

theorem thetaEquiv_slPair_mem_Jstar : thetaEquiv slPair ∈ Jstar := by
  refine ⟨thetaEquiv_mem_Gvis _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [tStar, ← PhiQ_seven]
  exact thetaEquiv_comm_rhoEquiv (conjQ_slPair_PhiQ _)

theorem ghat8_mem_Jhat :
    ghat8 ∈ Jhat := by
  rw [ghat8_eq, Jhat_eq_map]
  exact ⟨kappa slC, kappa_mem_Jbar thetaEquiv_slPair_mem_Jstar, rfl⟩

theorem ySqRowCheck_eq_true : ySqRowCheck Model.eYN = true :=
  Certificates.certificate3058

theorem Ymat_sq : Ymat ⟨toC 3, 0⟩ * Ymat ⟨toC 3, 0⟩ = 1 := by
  have h := ySqRowCheck_eq_true
  simp only [ySqRowCheck, List.all_eq_true, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, beq_iff_eq] at h
  refine matrix_eq_of_Evec fun η c hc => ?_
  rw [← Matrix.vecMul_vecMul, Evec_vecMul_Ymat, Matrix.smul_vecMul, Evec_vecMul_Ymat, smul_smul,
    Matrix.vecMul_one]
  have hc' := h c hc η (by cases η <;> simp)
  simp only [Prod.mk.injEq] at hc'
  obtain ⟨hs, hη, hcc⟩ := hc'
  rw [← sgn_boolZ_xor, hs, hη, hcc, Evec_pi0N, boolZ_false, show sgn (0 : ZMod 2) = 1 from rfl,
    one_smul]

theorem slPair_mul_self : slPair * slPair = 1 := by
  rw [slPair_eq]
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · apply Units.ext
    show Ymat ⟨toC 3, 0⟩ * Ymat ⟨toC 3, 0⟩ = 1
    exact Ymat_sq
  · exact gO_mul_self (toC 3)

theorem slC_mul_self :
    slC * slC = 1 := by
  apply Subtype.ext
  show thetaEquiv slPair * thetaEquiv slPair = 1
  rw [← thetaEquiv_mul, slPair_mul_self, thetaEquiv_one]

theorem ghat8_mul_self :
    ghat8 * ghat8 = 1 := by
  rw [ghat8_eq, ← map_mul, ← map_mul, slC_mul_self, map_one, map_one]

theorem jhatToKv0_ghat8 :
    jhatToKv0
    ⟨ghat8, ghat8_mem_Jhat⟩ = rK :=
    by
  apply Subtype.ext
  have he : (⟨ghat8, ghat8_mem_Jhat⟩ : Jhat) =
      jhatEquiv ⟨kappa slC, kappa_mem_Jbar thetaEquiv_slPair_mem_Jstar⟩ :=
    Subtype.ext ghat8_eq
  rw [he, jhatToKv0_jhatEquiv, coe_jbarToKv_kappa thetaEquiv_slPair_mem_Jstar rfl]
  show (QuotientGroup.mk (gO dC) : OLq)⁻¹ = alpha 12
  rw [alpha12_eq, ← QuotientGroup.mk_inv, inv_eq_of_mul_eq_one_right (gO_mul_self dC)]

theorem ghat8_not_mem_Ehat :
    ghat8 ∉ Ehat := by
  intro h
  have h1 := jhatToKv0_eq_one_of_mem_Ehat ghat8_mem_Jhat h
  rw [jhatToKv0_ghat8] at h1
  exact rK_ne_one h1

theorem ghat8_pow_add (a b : ZMod 2)
    :
    ghat8 ^ (a + b).val = ghat8 ^ a.val * ghat8 ^ b.val := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show ((1 : ZMod 2) + 1).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero,
      pow_one, ghat8_mul_self]

@[expose] def Psi
    (v : Fin 8 → ZMod 2) : Dfull := PhiD v * ghat8 ^
    (v 7).val

theorem Psi_add
    (v w : Fin 8 → ZMod 2)
    : Psi (v + w) = Psi v * Psi w
    := by
  have hc : Commute (ghat8 ^ (v 7).val) (PhiD w) :=
    Commute.pow_left (show Commute ghat8 (PhiD w) from ghat8_comm_PhiD w) _
  rw [Psi, Psi, Psi, PhiD_add, Pi.add_apply, ghat8_pow_add, mul_assoc, ← mul_assoc (PhiD w),
    ← hc.eq, mul_assoc, mul_assoc]

@[expose] def PsiHom :
    Multiplicative
    (Fin 8 → ZMod 2) →* Dfull where
  toFun v := Psi v.toAdd
  map_one' := by
    show PhiD 0 * ghat8 ^ ((0 : Fin 8 → ZMod 2) 7).val = 1
    rw [PhiD_zero, Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
  map_mul' v w := Psi_add v.toAdd w.toAdd

theorem PsiHom_apply
    (v : Multiplicative (Fin 8 → ZMod 2)) : PsiHom v
    = Psi v.toAdd := rfl

theorem Psi_single
    (k : Fin 8) : Psi (Pi.single k 1)
    = aT k := by
  by_cases hk : (k : ℕ) < 7
  · have h7 : (Pi.single k (1 : ZMod 2) : Fin 8 → ZMod 2) 7 = 0 :=
      Pi.single_eq_of_ne (fun h => by rw [← h] at hk; exact absurd hk (by decide)) _
    rw [Psi, h7, ZMod.val_zero, pow_zero, mul_one, PhiD_single hk]
  · have h7 : k = 7 := by
      ext
      show (k : ℕ) = 7
      have := k.2
      omega
    subst h7
    rw [Psi, PhiD_seven, one_mul, Pi.single_eq_same, show (1 : ZMod 2).val = 1 from rfl,
      pow_one]
    rfl

theorem Psi_injective
    (v : Fin 8 → ZMod 2)
    (h : Psi v = 1) : v = 0 :=
    by
  rcases zmod2_cases (v 7) with h0 | h1
  · rw [Psi, h0, ZMod.val_zero, pow_zero, mul_one] at h
    rcases (PhiD_eq_one_iff v).1 h with h' | h'
    · exact h'
    · exfalso
      rw [h', Pi.single_eq_same] at h0
      exact one_ne_zero h0
  · exfalso
    rw [Psi, h1, show (1 : ZMod 2).val = 1 from rfl, pow_one] at h
    have hg : ghat8 = (PhiD v)⁻¹ := eq_inv_of_mul_eq_one_right h
    apply ghat8_not_mem_Ehat
    rw [hg]
    exact Ehat.inv_mem (B7_le_Ehat (PhiD_mem_B7 v))

theorem ghat8_mem_A8 :
    ghat8 ∈ A8 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem B7_le_A8 :
    B7 ≤ A8 := fun _ hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)

theorem Psi_mem_A8
    (v : Fin 8 → ZMod 2) : Psi v ∈
    A8 :=
  A8.mul_mem (B7_le_A8 (PhiD_mem_B7 v)) (A8.pow_mem ghat8_mem_A8 _)

theorem PhiD_eq_Psi
    (v : Fin 8 → ZMod 2) : PhiD v = Psi
    (Function.update v 7 0) := by
  have hv : v = Function.update v 7 0 + Pi.single 7 (v 7) := by
    funext k
    by_cases hk : k = 7
    · subst hk
      simp
    · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]
  have hs : PhiD (Pi.single 7 (v 7)) = 1 := by
    rcases zmod2_cases (v 7) with h0 | h1
    · rw [h0, Pi.single_zero, PhiD_zero]
    · rw [h1, PhiD_seven]
  rw [Psi, Function.update_self, ZMod.val_zero, pow_zero, mul_one]
  conv_lhs => rw [hv]
  rw [PhiD_add, hs, mul_one]

theorem range_PsiHom :
    PsiHom.range =
    A8 := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Psi_mem_A8 v.toAdd
  · rw [A8, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact ⟨Multiplicative.ofAdd (Pi.single 7 1), Psi_single 7⟩
    · rw [B7_eq_range] at hx
      obtain ⟨v, rfl⟩ := hx
      exact ⟨Multiplicative.ofAdd (Function.update v.toAdd 7 0), (PhiD_eq_Psi v.toAdd).symm⟩

theorem PsiHom_injective :
    Function.Injective PsiHom := by
  rw [injective_iff_map_eq_one]
  intro v hv
  exact congrArg Multiplicative.ofAdd (Psi_injective v.toAdd hv)

@[expose] def aEquiv :
    Multiplicative
    (Fin 8 → ZMod 2) ≃* A8 :=
  (MonoidHom.ofInjective PsiHom_injective).trans (MulEquiv.subgroupCongr range_PsiHom)

theorem coe_aEquiv
    (v : Multiplicative (Fin 8 → ZMod 2)) :
    (aEquiv v : Dfull) = Psi v.toAdd :=
  rfl

theorem aEquiv_single
    (k : Fin 8) :
    (aEquiv (Multiplicative.ofAdd (Pi.single k 1)) : Dfull) = aT k := by
  rw [coe_aEquiv, toAdd_ofAdd, Psi_single]

theorem natCard_A8 :
    Nat.card A8 = 2 ^
    8 := by
  rw [← Nat.card_congr aEquiv.toEquiv]
  show Nat.card (Fin 8 → ZMod 2) = 2 ^ 8
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem A8_comm
    (x y : A8) : x * y = y
    * x := by
  obtain ⟨v, rfl⟩ := aEquiv.surjective x
  obtain ⟨w, rfl⟩ := aEquiv.surjective y
  rw [← map_mul, ← map_mul, mul_comm]

theorem A8_sq
    (x : A8) : x ^ 2 = 1 :=
    by
  obtain ⟨v, rfl⟩ := aEquiv.surjective x
  rw [← map_pow, show v ^ 2 = 1 from by
    rw [sq, ← ofAdd_toAdd v, ← ofAdd_add, ZModModule.add_self, ofAdd_zero], map_one]

instance isElementaryAbelian_A8 :
    CFSG.IsElementaryAbelian 2 A8 where
  is_comm := ⟨A8_comm⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one A8_sq

theorem A8_le_Jhat :
    A8 ≤ Jhat := by
  rw [A8, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact ghat8_mem_Jhat
  · exact Ehat_le_Jhat (B7_le_Ehat hx)

theorem A8_inf_Ehat :
    A8 ⊓ Ehat = B7
    := by
  apply le_antisymm
  · rintro x ⟨hx, he⟩
    rw [← range_PsiHom] at hx
    obtain ⟨v, rfl⟩ := hx
    rw [PsiHom_apply] at he ⊢
    rcases zmod2_cases (v.toAdd 7) with h0 | h1
    · rw [Psi, h0, ZMod.val_zero, pow_zero, mul_one]
      exact PhiD_mem_B7 _
    · exfalso
      rw [Psi, h1, show (1 : ZMod 2).val = 1 from rfl, pow_one] at he
      apply ghat8_not_mem_Ehat
      have := Ehat.mul_mem (Ehat.inv_mem (B7_le_Ehat (PhiD_mem_B7 v.toAdd))) he
      rwa [inv_mul_cancel_left] at this
  · exact le_inf B7_le_A8 B7_le_Ehat

theorem jhatToKv0_PhiD
    (v : Fin 8 → ZMod 2)
    (hv : PhiD v ∈ Jhat) :
    jhatToKv0 ⟨PhiD v, hv⟩ = 1 :=
  jhatToKv0_eq_one_of_mem_Ehat hv (B7_le_Ehat (PhiD_mem_B7 v))

theorem map_A8 :
    (A8.subgroupOf Jhat).map jhatToKv0 =
    Subgroup.zpowers rK := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hxJ⟩, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← range_PsiHom] at hx
    obtain ⟨v, rfl⟩ := hx
    have hP : PhiD v.toAdd ∈ Jhat := Ehat_le_Jhat (B7_le_Ehat (PhiD_mem_B7 _))
    have hg : ghat8 ^ (v.toAdd 7).val ∈ Jhat := Jhat.pow_mem ghat8_mem_Jhat _
    have e : (⟨PsiHom v, hxJ⟩ : Jhat) =
        ⟨PhiD v.toAdd, hP⟩ * ⟨ghat8, ghat8_mem_Jhat⟩ ^ (v.toAdd 7).val :=
      Subtype.ext rfl
    rw [e, map_mul, map_pow, jhatToKv0_PhiD, jhatToKv0_ghat8, one_mul]
    exact ⟨((v.toAdd 7).val : ℤ), zpow_natCast _ _⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨ghat8, ghat8_mem_Jhat⟩, ghat8_mem_A8, jhatToKv0_ghat8⟩

end CFSG.Monster.B.TwoA.Sp8
