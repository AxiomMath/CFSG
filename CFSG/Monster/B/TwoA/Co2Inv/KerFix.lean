
module

public import CFSG.Monster.B.TwoA.Co2Inv.KerFixBase

public import CFSG.Monster.B.TwoA.Co2Inv.KerElts
public import CFSG.Monster.B.TwoA.Co2Inv.SixAction

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

@[expose] def qParam :
    Fin 2 × Fin 16 × Fin 16 → Qgrp := fun x =>
  ⟨qElt x.1 x.2.1 x.2.2, mem_Qgrp_iff.2 ⟨x.1, x.1.2, x.2.1, x.2.1.2, x.2.2, x.2.2.2, rfl⟩⟩

theorem qParam_bijective :
    Function.Bijective qParam := by
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := qElt_inj x.1.2 x.2.1.2 x.2.2.2 y.1.2 y.2.1.2 y.2.2.2
      (congrArg Subtype.val h)
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
  · obtain ⟨e, he, l, hl, t, ht, h⟩ := mem_Qgrp_iff.1 z.2
    exact ⟨(⟨e, he⟩, ⟨l, hl⟩, ⟨t, ht⟩), Subtype.ext h.symm⟩

theorem natCard_Qgrp :
    Nat.card Qgrp = 512 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ qParam_bijective)]
  simp

theorem natCard_Agrp :
    Nat.card Agrp = 32 := by
  let f : Fin 2 × Fin 16 → Agrp := fun x =>
    ⟨qElt x.1 x.2 0, mem_Agrp_iff.2 ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => ?_, fun z => ?_⟩
    · obtain ⟨h1, h2, -⟩ := qElt_inj x.1.2 x.2.2 (by norm_num) y.1.2 y.2.2 (by norm_num)
        (congrArg Subtype.val h)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨e, he, l, hl, h⟩ := mem_Agrp_iff.1 z.2
      exact ⟨(⟨e, he⟩, ⟨l, hl⟩), Subtype.ext h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hf)]
  simp

theorem natCard_Tperm :
    Nat.card Tperm = 16 := by
  let f : Fin 16 → Tperm := fun t => ⟨transP t, transP_mem_Tperm t.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Fin.ext (transP_inj x.2 y.2 (congrArg Subtype.val h)), fun p => ?_⟩
    obtain ⟨t, ht, h⟩ := mem_Tperm_iff.1 p.2
    exact ⟨⟨t, ht⟩, Subtype.ext h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hf)]
  simp

theorem natCard_Tgrp :
    Nat.card Tgrp = 16 := by
  let f : Fin 16 → Tgrp := fun t => ⟨qElt 0 0 t, mem_Tgrp_iff.2 ⟨t, t.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => ?_, fun z => ?_⟩
    · obtain ⟨-, -, h3⟩ := qElt_inj (by norm_num) (by norm_num) x.2 (by norm_num) (by norm_num)
        y.2 (congrArg Subtype.val h)
      exact Fin.ext h3
    · obtain ⟨t, ht, h⟩ := mem_Tgrp_iff.1 z.2
      exact ⟨⟨t, ht⟩, Subtype.ext h.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hf)]
  simp

theorem affC_mem_Ceq {e l : ℕ} (he : e < 2) (hl : l < 16) :
    (affC e l : Fin 24 → ZMod 2) ∈ Ceq :=
  mem_Ceq.2 ⟨(affC e l).2, by
    rw [affC_apply_J (i := 0) he hl (by decide), affC_apply_J (i := 1) he hl (by decide)]⟩

theorem transP_mem_Foct {t : ℕ} (ht : t < 16) : transP t ∈ Foct :=
  Tperm_le_Foct (transP_mem_Tperm ht)

theorem qElt_mem_Kstab
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    qElt e l t ∈ Kstab v0 :=
  (mk_mem_Kstab_iff_monomial _ _).2 ⟨Foct_le_Ppair (transP_mem_Foct ht), affC_mem_Ceq he hl⟩

@[expose] def qK
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) : Kstab v0 :=
  ⟨qElt e l t, qElt_mem_Kstab he hl ht⟩

theorem qK_mem_Mr
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) : qK he hl ht ∈ Mr :=
  (mem_Mr_iff _).2 ((mem_monoSub_iff foctHyp).2
    ⟨affC e l, affC_mem_Ceq he hl, transP t, transP_mem_Foct ht, rfl⟩)

theorem qK_mem_Cr
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) : qK he hl ht ∈ Cr :=
  Mr_le_Cr (qK_mem_Mr he hl ht)

theorem exists_Cr_of_mem_Qgrp
    {x : OLq} (hx : x ∈ Qgrp) :
    ∃ k : Cr, ((k : Kstab v0) : OLq) = x := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := mem_Qgrp_iff.1 hx
  exact ⟨⟨qK he hl ht, qK_mem_Cr he hl ht⟩, rfl⟩

theorem mk_gO_affC_mem_Kstab
    {e l : ℕ} (he : e < 2) (hl : l < 16) :
    (QuotientGroup.mk (gO (affC e l)) : OLq) ∈ Kstab v0 := by
  have h := qElt_mem_Kstab he hl (by norm_num : 0 < 16)
  rwa [qElt, transP_zero, PO_one, mul_one] at h

theorem sign_fix_zVec
    {e l : ℕ} (he : e < 2) (hl : l < 16) (s : Fin 6) :
    wAct v0 ⟨_, mk_gO_affC_mem_Kstab he hl⟩ (zVec s) = zVec s := by
  have hi := affIdx_lt e he l hl
  exact wAct_zVec_of_rows _ (kOp_sign_dec (coe_affC he hl) (mk_gO_affC_mem_Kstab he hl)
    (signRows_ok _ hi).1) (signRows_ok _ hi).2 s

theorem perm_fix_zVec
    {t : ℕ} (ht : t < 16) (s : Fin 6) :
    wAct v0 (permK (Foct_le_Ppair (transP_mem_Foct ht))) (zVec s) = zVec s := by
  have hj := translationLabels_lt t ht
  exact wAct_zVec_of_rows _ (kOp_permK_dec (transArr_perm ht).1 (coe_transP ht)
    (Foct_le_Ppair (transP_mem_Foct ht)) (transRows_ok _ hj).1) (transRows_ok _ hj).2 s

theorem qK_fix_Zsp
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) {z : Wv v0}
    (hz : z ∈ Zsp) : wAct v0 (qK he hl ht) z = z := by
  have hsplit : qK he hl ht =
      ⟨_, mk_gO_affC_mem_Kstab he hl⟩ * permK (Foct_le_Ppair (transP_mem_Foct ht)) := by
    apply Subtype.ext
    change qElt e l t = QuotientGroup.mk (gO (affC e l)) * QuotientGroup.mk (PO (transP t))
    rw [qElt, QuotientGroup.mk_mul]
  refine wAct_eq_of_zVec _ (fun s => ?_) hz
  rw [hsplit, wAct_mul, Module.End.mul_apply, sign_fix_zVec he hl s, perm_fix_zVec ht s]

theorem resZ_eq_one_iff
    (k : Cr) :
    resZ k = 1 ↔ ∀ z ∈ Zsp, wAct v0 (k : Kstab v0)⁻¹ z = z := by
  constructor
  · intro h z hz
    have := congrArg (fun φ : TauCeti.BilinForm.isometryGroup bZ =>
      (((φ : Zsp ≃ₗ[ZMod 2] Zsp) ⟨z, hz⟩ : Zsp) : Wv v0)) h
    simpa only [coe_resZ_apply, OneMemClass.coe_one, LinearEquiv.coe_one, id] using this
  · intro h
    refine Subtype.ext (LinearEquiv.ext fun x => Subtype.ext ?_)
    simpa only [coe_resZ_apply, OneMemClass.coe_one, LinearEquiv.coe_one, id] using h x x.2

theorem resZ_eq_one_of_fix
    (k : Cr) (h : ∀ z ∈ Zsp, wAct v0 (k : Kstab v0) z = z) :
    resZ k = 1 := by
  refine (resZ_eq_one_iff k).2 fun z hz => ?_
  conv_lhs => rw [← h z hz]
  exact wAct_inv_apply _ z

@[expose] def QCr :
    Subgroup Cr := Qgrp.comap ((Kstab v0).subtype.comp Cr.subtype)

theorem mem_QCr
    {k : Cr} : k ∈ QCr ↔ ((k : Kstab v0) : OLq) ∈ Qgrp := Iff.rfl

theorem fix_of_mem_QCr
    {k : Cr} (hk : k ∈ QCr) : ∀ z ∈ Zsp, wAct v0 (k : Kstab v0) z = z := by
  obtain ⟨e, he, l, hl, t, ht, h⟩ := mem_Qgrp_iff.1 (mem_QCr.1 hk)
  have hk' : (k : Kstab v0) = qK he hl ht := Subtype.ext h
  intro z hz
  rw [hk']
  exact qK_fix_Zsp he hl ht hz

theorem resZ_one_of_mem_QCr
    {k : Cr} (hk : k ∈ QCr) : resZ k = 1 :=
  resZ_eq_one_of_fix k (fix_of_mem_QCr hk)

theorem QCr_le_ker :
    QCr ≤ resZ.ker := fun _ hk => MonoidHom.mem_ker.2 (resZ_one_of_mem_QCr hk)

theorem natCard_QCr :
    Nat.card QCr = 512 := by
  rw [← natCard_Qgrp]
  refine Nat.card_congr (Equiv.ofBijective (fun k => ⟨((k.1 : Kstab v0) : OLq), k.2⟩)
    ⟨fun x y h => ?_, fun z => ?_⟩)
  · have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  · obtain ⟨k, hk⟩ := exists_Cr_of_mem_Qgrp z.2
    exact ⟨⟨k, mem_QCr.2 (hk ▸ z.2)⟩, Subtype.ext hk⟩

theorem QCr_eq_ker :
    QCr = resZ.ker :=
  Subgroup.eq_of_le_of_card_ge QCr_le_ker
    (resZ_surjective_natCard_ker.2.1.trans natCard_QCr.symm).le

theorem mem_ker_resZ_iff
    (k : Cr) : k ∈ resZ.ker ↔ ((k : Kstab v0) : OLq) ∈ Qgrp := by
  rw [← QCr_eq_ker, mem_QCr]

end CFSG.Monster.B.TwoA.Co2Inv
