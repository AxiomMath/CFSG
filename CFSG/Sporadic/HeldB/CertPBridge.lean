module

public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.HeldB.CertPBridgeCheck
public import CFSG.Sporadic.He.Simple

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

@[expose] def heBridgePerm : Equiv.Perm (Fin 8330) := permOfArr 8330 heBridgeArr

theorem orb_eq : CFSG.Sporadic.He.orb = CFSG.Sporadic.He.Native.orbitData () := rfl

theorem heBridge_parts' :
    isInvA 8330 heBridgeArr (invCand 8330 heBridgeArr) = true ∧
    (∀ i < 8330, ap (CFSG.Sporadic.He.Native.orbitData ()).alpha heBridgeArr[i]! =
      heBridgeArr[(heGen 0)[i]!]!) ∧
    (∀ i < 8330, ap (CFSG.Sporadic.He.Native.orbitData ()).beta heBridgeArr[i]! =
      heBridgeArr[(heGen 1)[i]!]!) := by
  have h := heBridge_check
  rw [heBridgeOK] at h
  simp only [Bool.and_eq_true, allLt_iff, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem heBridge_parts :
    isInvA 8330 heBridgeArr (invCand 8330 heBridgeArr) = true ∧
    (∀ i < 8330, ap CFSG.Sporadic.He.orb.alpha heBridgeArr[i]! =
      heBridgeArr[(heGen 0)[i]!]!) ∧
    (∀ i < 8330, ap CFSG.Sporadic.He.orb.beta heBridgeArr[i]! =
      heBridgeArr[(heGen 1)[i]!]!) := by
  rw [orb_eq]
  exact heBridge_parts'

theorem rep_heBridge : Rep 8330 heBridgeArr heBridgePerm :=
  (rep_permOfArr heBridge_parts.1).1

@[expose] def heJPerm :
    CFSG.Sporadic.He.J →* Equiv.Perm (Fin 8330) :=
  MulAction.toPermHom CFSG.Sporadic.He.J (Fin 8330)

theorem heJPerm_apply
    (g : CFSG.Sporadic.He.J) (i : Fin 8330) : heJPerm g i = g • i := rfl

theorem perm_inv_apply_self (f : Equiv.Perm (Fin 8330)) (x : Fin 8330) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem perm_apply_inv_self (f : Equiv.Perm (Fin 8330)) (x : Fin 8330) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

@[expose] def heJConj
    (x : Equiv.Perm (Fin 8330)) : CFSG.Sporadic.He.J →* Equiv.Perm (Fin 8330) :=
  (MulAut.conj x⁻¹).toMonoidHom.comp heJPerm

theorem heJConj_apply
    (x : Equiv.Perm (Fin 8330)) (g : CFSG.Sporadic.He.J) (i : Fin 8330) :
    heJConj x g i = x⁻¹ (g • x i) := by
  rw [heJConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, heJPerm_apply]

theorem smul_val_of_rep
    {T : CFSG.Sporadic.Th.Native.Table} {g : CFSG.Sporadic.He.J}
    (hT : CFSG.Sporadic.Th.Rep 8330 T g) (i : Fin 8330) : (g • i).val = ap T i.val := by
  rw [hT i.val i.isLt, CFSG.Sporadic.Th.idx_of_lt g i.isLt]

theorem heJConj_gen
    {x : Equiv.Perm (Fin 8330)} (hx : Rep 8330 heBridgeArr x) {k : ℕ}
    (hk : k < 2) {T : CFSG.Sporadic.Th.Native.Table} {g : CFSG.Sporadic.He.J}
    (hT : CFSG.Sporadic.Th.Rep 8330 T g)
    (hcheck : ∀ i < 8330, ap T heBridgeArr[i]! = heBridgeArr[(heGen k)[i]!]!) :
    heJConj x g = heGenPerm k := by
  refine Equiv.ext fun i => ?_
  rw [heJConj_apply]
  have h1 : g • x i = x (heGenPerm k i) := by
    apply Fin.ext
    rw [smul_val_of_rep hT, ← hx (heGenPerm k i), ← hx i, ← rep_heGen hk i]
    exact hcheck i.val i.isLt
  rw [h1, perm_inv_apply_self]

theorem heJConj_injective
    (x : Equiv.Perm (Fin 8330)) : Function.Injective (heJConj x) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply CFSG.Sporadic.He.eq_one_of_fix_all
  intro i
  have h : heJConj x g (x⁻¹ i) = (1 : Equiv.Perm (Fin 8330)) (x⁻¹ i) := by
    rw [hg]
  rw [heJConj_apply, perm_apply_inv_self, Equiv.Perm.one_apply] at h
  have h2 := congrArg x h
  rwa [perm_apply_inv_self, perm_apply_inv_self] at h2

@[expose] def heJToP :
    CFSG.Sporadic.He.J →* Equiv.Perm (Fin 8330) := heJConj heBridgePerm

theorem heJToP_apply (g : CFSG.Sporadic.He.J) (i : Fin 8330) :
    heJToP g i = heBridgePerm⁻¹ (g • heBridgePerm i) :=
  heJConj_apply heBridgePerm g i

theorem heJToP_a :
    heJToP CFSG.Sporadic.He.a = heGenPerm 0 :=
  heJConj_gen rep_heBridge (by norm_num) CFSG.Sporadic.He.rep_alpha heBridge_parts.2.1

theorem heJToP_b :
    heJToP CFSG.Sporadic.He.b = heGenPerm 1 :=
  heJConj_gen rep_heBridge (by norm_num) CFSG.Sporadic.He.rep_beta heBridge_parts.2.2

theorem heJToP_injective :
    Function.Injective heJToP := heJConj_injective heBridgePerm

theorem heJToP_range :
    heJToP.range = heP := by
  rw [MonoidHom.range_eq_map, ← CFSG.Sporadic.He.closure_ab, MonoidHom.map_closure, heP]
  congr 1
  rw [Set.image_pair, heJToP_a, heJToP_b]

@[expose] def heJEquivP :
    CFSG.Sporadic.He.J ≃* heP :=
  (MonoidHom.ofInjective heJToP_injective).trans (MulEquiv.subgroupCongr heJToP_range)

theorem heJEquivP_apply
    (g : CFSG.Sporadic.He.J) : (heJEquivP g : Equiv.Perm (Fin 8330)) =
    heJToP g := rfl

@[expose] def heEquivP :
    Blueprint.NativeSporadic.He ≃* heP :=
  CFSG.Sporadic.He.heEquivJ.trans heJEquivP

theorem heEquivP_seed1
    (x : Blueprint.NativeSporadic.He)
    (hx : x.val.val = Blueprint.NativeSporadic.decode 7 50 1 Blueprint.NativeSporadic.HeSeed1) :
    (heEquivP x : Equiv.Perm (Fin 8330)) = heGenPerm 0 := by
  have h : CFSG.Sporadic.He.heEquivJ x = CFSG.Sporadic.He.a := by
    apply CFSG.Sporadic.He.mat_injective
    rw [CFSG.Sporadic.He.mat_heEquivJ, hx, CFSG.Sporadic.He.mat_a]
  rw [heEquivP, MulEquiv.trans_apply, h, heJEquivP_apply, heJToP_a]

theorem heEquivP_seed2
    (x : Blueprint.NativeSporadic.He)
    (hx : x.val.val = Blueprint.NativeSporadic.decode 7 50 1 Blueprint.NativeSporadic.HeSeed2) :
    (heEquivP x : Equiv.Perm (Fin 8330)) = heGenPerm 1 := by
  have h : CFSG.Sporadic.He.heEquivJ x = CFSG.Sporadic.He.b := by
    apply CFSG.Sporadic.He.mat_injective
    rw [CFSG.Sporadic.He.mat_heEquivJ, hx, CFSG.Sporadic.He.mat_b]
  rw [heEquivP, MulEquiv.trans_apply, h, heJEquivP_apply, heJToP_b]

theorem heP_simple :
    IsSimpleGroup heP :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He heEquivP.symm

end CFSG.Sporadic.HeldB
