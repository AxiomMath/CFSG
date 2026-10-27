module

public import CFSG.Monster.B.TwoA.Base.PairStab
public import CFSG.Monster.B.TwoA.Base.Mono
public import CFSG.Monster.B.TwoA.Base.PairCls
public import CFSG.Monster.B.TwoA.Base.WActBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

@[expose] def coordEq (i j : Fin 24) : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  LinearMap.ker ((LinearMap.proj i : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) - LinearMap.proj j)

theorem mem_coordEq {i j : Fin 24} {x : Fin 24 → ZMod 2} : x ∈ coordEq i j ↔ x i = x j := by
  rw [coordEq, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply,
    LinearMap.proj_apply, sub_eq_zero]

@[expose] def Ceq : Submodule (ZMod 2) (Fin 24 → ZMod 2) := C ⊓ coordEq 0 1

theorem mem_Ceq {x : Fin 24 → ZMod 2} : x ∈ Ceq ↔ x ∈ C ∧ x 0 = x 1 := by
  rw [Ceq, Submodule.mem_inf, mem_coordEq]

theorem permWord_apply' (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) (i : Fin 24) :
    permWord p x i = x (p⁻¹ i) := rfl

theorem coe_inv_autPerm (p : AutPerm) :
    ((p⁻¹ : AutPerm) : Equiv.Perm (Fin 24)) = (p : Equiv.Perm (Fin 24))⁻¹ := rfl

theorem ceqHyp : MonoHyp Ceq Ppair where
  le_C := inf_le_left
  Ω_mem := mem_Ceq.2 ⟨Ω_mem_C, rfl⟩
  preserves p hp a ha := by
    rw [mem_Ceq] at ha ⊢
    refine ⟨permWord_mem_of_mem_AutPerm p.2 ha.1, ?_⟩
    rw [permWord_apply', permWord_apply']
    have hp' := Ppair.inv_mem hp
    rcases (mem_Ppair_iff p⁻¹).1 hp' with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [← coe_inv_autPerm, h0, h1]
      exact ha.2
    · rw [← coe_inv_autPerm, h0, h1]
      exact ha.2.symm

@[expose] def ceqForm : C →ₗ[ZMod 2] ZMod 2 :=
  ((LinearMap.proj 0 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) - LinearMap.proj 1).comp C.subtype

theorem ceqForm_surjective : Function.Surjective ceqForm := by
  intro t
  refine ⟨t • ⟨B 1, B_mem_C 1⟩, ?_⟩
  rw [map_smul]
  have h : ceqForm ⟨B 1, B_mem_C 1⟩ = B 1 0 - B 1 1 := rfl
  rw [h, show B 1 0 - B 1 1 = 1 by decide, smul_eq_mul, mul_one]

theorem comap_Ceq : Ceq.comap C.subtype = LinearMap.ker ceqForm := by
  ext c
  simp only [Submodule.mem_comap, Submodule.subtype_apply, mem_Ceq, LinearMap.mem_ker, ceqForm,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero]
  exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩

theorem finrank_Ceq : Module.finrank (ZMod 2) Ceq = 11 := by
  have h := LinearMap.finrank_range_add_finrank_ker ceqForm
  rw [LinearMap.range_eq_top.2 ceqForm_surjective, finrank_top, Module.finrank_self,
    finrank_C, ← comap_Ceq] at h
  have e := (Submodule.comapSubtypeEquivOfLe (p := Ceq) (q := C) inf_le_left).finrank_eq
  omega

theorem natCard_Ceq_quot : Nat.card (Ceq ⧸ ΩIn Ceq) = 2 ^ 10 := by
  rw [natCard_quot_ΩIn ceqHyp, finrank_Ceq]

theorem v0_eq_pairCls : v0 = pairCls 0 1 0 := by
  rw [pairCls, pairVec_zero]

theorem bL_v0_twoΩCls :
    bL v0 twoΩCls = 0 := by
  rw [v0, classOf_of_mem vMinus_zero_one_mem.1, twoΩCls, cls, bL_mk, hInt]
  change ((((∑ i, Griess.vMinus 0 1 i * Visible.twoΩ i) / 8 : ℤ)) : ZMod 2) = 0
  rw [sum_vMinus_mul]
  rfl

theorem twoΩCls_mem_vPerpL :
    twoΩCls ∈ vPerpL v0 := bL_v0_twoΩCls

@[expose] def fPerp :
    vPerpL v0 := ⟨twoΩCls, twoΩCls_mem_vPerpL⟩

@[expose] def wFr :
    Wv v0 := Submodule.Quotient.mk fPerp

theorem twoΩCls_not_short : twoΩCls ∉ VisCert.shortSet := VisCert.twoΩCls_mem_frameDelta.2.2

theorem v0_short : v0 ∈ VisCert.shortSet := ⟨_, vMinus_zero_one_mem, rfl⟩

theorem twoΩCls_ne_v0 : twoΩCls ≠ v0 := fun h => twoΩCls_not_short (h ▸ v0_short)

theorem wFr_ne_zero :
    wFr ≠ 0 := by
  rw [wFr, Ne, mk_eq_zero_iff]
  rintro (h | h)
  · exact twoΩCls_ne_zero h
  · exact twoΩCls_ne_v0 h

@[expose] def Mfr :
    Subgroup (Kstab v0) := wStab wFr

theorem kOp_mem_shortSet_iff (k : OLq) {x : L2} :
    kOp k x ∈ VisCert.shortSet ↔ x ∈ VisCert.shortSet := by
  induction k using QuotientGroup.induction_on with
  | H g =>
    rw [kOp_mk]
    refine ⟨fun h => ?_, VisCert.modTwoEnd_mem_shortSet g⟩
    rw [← VisCert.modTwoEnd_inv_apply g x]
    exact VisCert.modTwoEnd_mem_shortSet g⁻¹ h

theorem twoΩCls_add_v0 :
    twoΩCls + v0 = pairCls 0 1 1 := by
  rw [v0_eq_pairCls, twoΩCls_add_pairCls (by decide)]
  rfl

theorem mem_Mfr_iff_fix
    (k : Kstab v0) : k ∈ Mfr ↔ kOp k twoΩCls = twoΩCls := by
  rw [Mfr, mem_wStab, wFr, wAct_mk]
  constructor
  · intro h
    rw [Submodule.Quotient.eq] at h
    have h' : kOp k twoΩCls - twoΩCls ∈ vLineL v0 := h
    rcases mem_vLineL.1 h' with h0 | h1
    · exact sub_eq_zero.1 h0
    · exfalso
      have e : kOp k twoΩCls = twoΩCls + v0 :=
        (sub_eq_iff_eq_add.1 h1).trans (add_comm _ _)
      have hs : kOp k twoΩCls ∈ VisCert.shortSet := by
        rw [e, twoΩCls_add_v0]
        exact pairCls_mem_shortSet (by decide) 1
      exact twoΩCls_not_short ((kOp_mem_shortSet_iff (k : OLq)).1 hs)
  · intro h
    congr 1
    exact Subtype.ext h

theorem mk_mem_Kstab_iff_monomial
    (a : C) (p : AutPerm) :
    (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 ↔
      p ∈ Ppair ∧ (a : Fin 24 → ZMod 2) ∈ Ceq := by
  rw [mk_mem_Kstab_iff, v0_eq_pairCls, modTwoEnd_gO_mul_PO_pairCls a p (by decide),
    pairCls_eq_iff ((p : Equiv.Perm (Fin 24)).injective.ne (by decide)) (by decide), mem_Ppair_iff,
    mem_Ceq]
  have hc0 : ∀ s t : ZMod 2, (0 + s + t = 0 ↔ s = t) := by decide
  rw [hc0]
  exact ⟨fun h => ⟨h.1, a.2, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

theorem monoSub_ceq_le_Kstab :
    monoSub ceqHyp ≤ Kstab v0 := by
  intro x hx
  obtain ⟨a, ha, p, hp, rfl⟩ := (mem_monoSub_iff ceqHyp).1 hx
  exact (mk_mem_Kstab_iff_monomial a p).2 ⟨hp, ha⟩

theorem mem_Mfr_iff
    (k : Kstab v0) : k ∈ Mfr ↔ (k : OLq) ∈ monoSub ceqHyp := by
  rw [mem_Mfr_iff_fix]
  constructor
  · intro h
    have hf : (k : OLq) ∈ stabQ := h
    obtain ⟨a, p, hap⟩ := mem_stabQ_iff.1 hf
    have hk := k.2
    rw [hap, mk_mem_Kstab_iff_monomial] at hk
    rw [hap]
    exact mk_mem_monoSub ceqHyp hk.2 hk.1
  · intro h
    exact monoSub_le_stabQ ceqHyp h

theorem map_Mfr :
    Mfr.map (Kstab v0).subtype = monoSub ceqHyp := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_Mfr_iff k).1 hk
  · intro hx
    exact ⟨⟨x, monoSub_ceq_le_Kstab hx⟩, (mem_Mfr_iff _).2 hx, rfl⟩

@[expose] def mfrEquivMono :
    Mfr ≃* monoSub ceqHyp :=
  (Mfr.equivMapOfInjective (Kstab v0).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr map_Mfr)

theorem coe_mfrEquivMono
    (k : Mfr) : (mfrEquivMono k : OLq) = ((k : Kstab v0) : OLq) := rfl

@[expose] def MfrEquiv :

    SDD ceqHyp ≃* Mfr := (monoSubEquiv ceqHyp).trans mfrEquivMono.symm

theorem coe_MfrEquiv
    (x : SDD ceqHyp) :
    ((MfrEquiv x : Kstab v0) : OLq) = monoD ceqHyp x := by
  have h := coe_mfrEquivMono (MfrEquiv x)
  rw [MfrEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem mem_monoSub_ceq_iff
    {k : OLq} (hk : k ∈ Kstab v0) :
    k ∈ monoSub ceqHyp ↔ kOp k twoΩCls = twoΩCls :=
  (mem_Mfr_iff ⟨k, hk⟩).symm.trans (mem_Mfr_iff_fix ⟨k, hk⟩)

theorem kOp_sub_mem_vLineL_iff
    {k : OLq} (hk : k ∈ Kstab v0) :
    kOp k twoΩCls - twoΩCls ∈ vLineL v0 ↔ kOp k twoΩCls = twoΩCls := by
  constructor
  · intro h
    refine (mem_Mfr_iff_fix ⟨k, hk⟩).1 ?_
    rw [Mfr, mem_wStab, wFr, wAct_mk, Submodule.Quotient.eq]
    exact h
  · intro h
    rw [h, sub_self]
    exact zero_mem _

theorem natCard_Mfr :
    Nat.card Mfr = 908328960 := by
  rw [Nat.card_congr mfrEquivMono.toEquiv, natCard_monoSub, natCard_Ceq_quot, natCard_Ppair]
  norm_num

end CFSG.Monster.B.TwoA
