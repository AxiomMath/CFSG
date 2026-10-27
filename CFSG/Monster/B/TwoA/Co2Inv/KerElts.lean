
module

public import CFSG.Monster.B.TwoA.Co2Inv.KerEltsBase

public import CFSG.Monster.B.TwoA.Co2Inv.KerData
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrder
public import CFSG.Monster.B.TwoA.Co2Inv.KerDataBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem affMask_mem_C
    {e l : ℕ} (he : e < 2) (hl : l < 16) : bvec 24 (affMask e l) ∈ C :=
  shortCode_mem_C _ (affIdx_lt e he l hl)

theorem coe_affC {e l : ℕ} (he : e < 2) (hl : l < 16) :
    (affC e l : Fin 24 → ZMod 2) = bvec 24 (affMask e l) := by
  rw [affC, dite_eq_left (affMask_mem_C he hl)]

theorem affC_zero : affC 0 0 = 0 :=
  Subtype.ext (by rw [coe_affC (by norm_num) (by norm_num), affMask_zero, bvec_zero]; rfl)

theorem affC_add
    {e l e' l' : ℕ} (he : e < 2) (hl : l < 16) (he' : e' < 2) (hl' : l' < 16) :
    affC e l + affC e' l' = affC (e ^^^ e') (l ^^^ l') := by
  apply Subtype.ext
  rw [Submodule.coe_add, coe_affC he hl, coe_affC he' hl',
    coe_affC (xor_lt_two he he') (xor_lt_sixteen hl hl'), ← bvec_xor,
    affMask_xor e he l hl e' he' l' hl']

theorem affC_apply_J
    {e l : ℕ} (he : e < 2) (hl : l < 16) {i : Fin 24} (hi : (i : ℕ) < 8) :
    (affC e l : Fin 24 → ZMod 2) i = 0 := by
  rw [coe_affC he hl, bvec_apply, affMask_J e he l hl i hi]
  rfl

theorem affC_mem_CJc {e l : ℕ} (he : e < 2) (hl : l < 16) :
    (affC e l : Fin 24 → ZMod 2) ∈ CJc (dC : Fin 24 → ZMod 2) :=
  ⟨(affC e l).2, fun i hi => (dC_apply_eq_zero i).2 fun h => hi (affC_apply_J he hl h)⟩

theorem affC_inj
    {e l e' l' : ℕ} (he : e < 2) (hl : l < 16) (he' : e' < 2) (hl' : l' < 16)
    (h : affC e l = affC e' l') : e = e' ∧ l = l' := by
  have h' := congrArg (fun c : C => (c : Fin 24 → ZMod 2)) h
  simp only [coe_affC he hl, coe_affC he' hl'] at h'
  exact affMask_inj he hl he' hl'
    (bvec_injective (affMask_lt e he l hl) (affMask_lt e' he' l' hl') h')

theorem mem_CJc_iff {c : Fin 24 → ZMod 2} :
    c ∈ CJc (dC : Fin 24 → ZMod 2) ↔ ∃ e < 2, ∃ l < 16, c = (affC e l : Fin 24 → ZMod 2) := by
  constructor
  · intro hc
    let f : Fin 2 × Fin 16 → CJc (dC : Fin 24 → ZMod 2) :=
      fun x => ⟨affC x.1 x.2, affC_mem_CJc x.1.2 x.2.2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h := congrArg (fun z : CJc (dC : Fin 24 → ZMod 2) => (z : Fin 24 → ZMod 2)) hxy
      obtain ⟨h1, h2⟩ := affC_inj x.1.2 x.2.2 y.1.2 y.2.2 (Subtype.ext h)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    have hcard : Nat.card (CJc (dC : Fin 24 → ZMod 2)) ≤ Nat.card (Fin 2 × Fin 16) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_CJc dC.2 hammingNorm_dC,
        Nat.card_zmod, Nat.card_prod, Nat.card_fin, Nat.card_fin]
      norm_num
    obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨c, hc⟩
    exact ⟨x.1, x.1.2, x.2, x.2.2, (congrArg Subtype.val hx).symm⟩
  · rintro ⟨e, he, l, hl, rfl⟩
    exact affC_mem_CJc he hl

theorem transArr_perm
    {t : ℕ} (ht : t < 16) : PermArr (transArr t) = true ∧ AutArr (transArr t) :=
  octPerms_perm _ (translationLabels_lt t ht)

@[expose] def transP (t : ℕ) : AutPerm :=
  if h : t < 16 then
    ⟨decode (transArr t), mem_AutPerm_of_arr (transArr_perm h).1 (transArr_perm h).2⟩
  else 1

theorem coe_transP {t : ℕ} (ht : t < 16) :
    ((transP t : AutPerm) : Equiv.Perm (Fin 24)) = decode (transArr t) := by
  rw [transP, dite_eq_left ht]

theorem transP_apply {t : ℕ} (ht : t < 16) (x : Fin 24) :
    (((transP t : AutPerm) : Equiv.Perm (Fin 24)) x : ℕ) = (transArr t)[(x : ℕ)]! := by
  rw [coe_transP ht, decode_apply (transArr_perm ht).1]

theorem transP_zero : transP 0 = 1 := by
  apply Subtype.ext
  rw [coe_transP (by norm_num), transArr_zero, decode_idArr]
  rfl

theorem transP_mul {t t' : ℕ} (ht : t < 16) (ht' : t' < 16) :
    transP t' * transP t = transP (t ^^^ t') := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_transP ht', coe_transP ht, coe_transP (xor_lt_sixteen ht ht'),
    ← decode_amul (transArr_perm ht').1 (transArr_perm ht).1, transArr_mul t ht t' ht']

theorem transP_inj
    {t t' : ℕ} (ht : t < 16) (ht' : t' < 16) (h : transP t = transP t') :
    t = t' := by
  have h' := congrArg (fun p : AutPerm => (p : Equiv.Perm (Fin 24))) h
  simp only [coe_transP ht, coe_transP ht'] at h'
  exact transArr_inj t ht t' ht' (decode_inj (transArr_perm ht).1 (transArr_perm ht').1 h')

theorem transP_fixJ
    {t : ℕ} (ht : t < 16) {x : Fin 24} (hx : (x : ℕ) < 8) :
    ((transP t : AutPerm) : Equiv.Perm (Fin 24)) x = x :=
  Fin.ext ((transP_apply ht x).trans (transArr_fixJ t ht x hx))

theorem permC_symm_affC
    {t e l : ℕ} (ht : t < 16) (he : e < 2) (hl : l < 16) :
    (permC (transP t)).symm (affC e l) = affC (e ^^^ par4 (l &&& t)) l := by
  apply Subtype.ext
  funext x
  rw [permC_symm_apply, coe_permC, permWord_apply', coe_inv_autPerm, inv_inv,
    coe_affC (xor_lt_two he (par4_lt _)) hl, coe_affC he hl, bvec_apply, bvec_apply]
  have hx : (((transP t : AutPerm) : Equiv.Perm (Fin 24)) x : ℕ) = (transArr t)[(x : ℕ)]! :=
    transP_apply ht x
  rw [hx, transArr_sign t ht e he l hl x x.2]

theorem transP_mem_Tperm {t : ℕ} (ht : t < 16) : transP t ∈ Tperm :=
  fun _ hi => transP_fixJ ht hi

theorem mem_Tperm_iff
    {p : AutPerm} : p ∈ Tperm ↔ ∃ t < 16, p = transP t := by
  constructor
  · intro hp
    have hF : (p : Equiv.Perm (Fin 24)) ∈ F9 := by
      rw [← map_F9A, natCard_Foct.2]
      exact Subgroup.mem_map.2 ⟨p, Tperm_le_Foct hp, rfl⟩
    obtain ⟨i, hi, hpi⟩ := (F9_facts.2 _).1 hF
    have hi' : i < fCert.pts.size := by rw [fCheck_parts.2.1]; exact hi
    have hperm := certOK_perm fCheck_parts.1 hi'
    have hfix : fixJ fCert.pts[i]! = true := by
      refine fixJ_eq_true hperm fun x hx => ?_
      rw [← pt, hpi]
      exact hp x hx
    have hmem : akey fCert.pts[i]! ∈ (fCert.pts.toList.filter fixJ).map akey := by
      refine List.mem_map.2 ⟨fCert.pts[i]!, List.mem_filter.2 ⟨?_, hfix⟩, rfl⟩
      rw [getElem!_pos fCert.pts i hi']
      exact Array.getElem_mem_toList hi'
    rw [← List.mem_mergeSort (le := fun a b => decide (a ≤ b)), fCheck_parts.2.2,
      List.mem_mergeSort, List.mem_map] at hmem
    obtain ⟨q, hq, hqk⟩ := hmem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hj16 : j < 16 := by
      rw [Array.length_toList, octPerms_size] at hj
      exact hj
    have hqj : octPerms.toList[j]'hj = octPerms[j]! := by
      rw [getElem!_pos octPerms j (by rw [octPerms_size]; exact hj16)]
      exact Array.getElem_toList hj
    rw [hqj] at hqk
    have heq := akey_inj (octPerms_perm j hj16).1 hperm hqk
    obtain ⟨hlt, htr⟩ := translationLabels_spec j hj16
    refine ⟨translationLabels[j]!, hlt, Subtype.ext ?_⟩
    rw [coe_transP hlt, htr, heq, ← pt, hpi]
  · rintro ⟨t, ht, rfl⟩
    exact transP_mem_Tperm ht

@[expose] def qElt
    (e l t : ℕ) : OLq := QuotientGroup.mk (gO (affC e l) * PO (transP t))

theorem qElt_mul
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) :
    qElt e l t * qElt e' l' t' = qElt (e ^^^ e' ^^^ par4 (l' &&& t)) (l ^^^ l') (t ^^^ t') := by
  unfold qElt
  rw [← QuotientGroup.mk_mul]
  congr 1
  have h1 : gO (affC e l) * PO (transP t) * (gO (affC e' l') * PO (transP t')) =
      gO (affC e l + (permC (transP t)).symm (affC e' l')) * PO (transP t' * transP t) := by
    rw [gO_add, PO_mul, ← mul_assoc, mul_assoc (gO (affC e l)), PO_mul_gO, ← mul_assoc,
      mul_assoc _ (PO (transP t))]
  rw [h1, permC_symm_affC ht he' hl', affC_add he hl (xor_lt_two he' (par4_lt _)) hl',
    transP_mul ht ht', Nat.xor_assoc]

theorem qElt_zero : qElt 0 0 0 = 1 := by
  rw [qElt, affC_zero, transP_zero, gO_zero, PO_one, one_mul, QuotientGroup.mk_one]

theorem qElt_sq
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    qElt e l t * qElt e l t = qElt (par4 (l &&& t)) 0 0 := by
  rw [qElt_mul he hl ht he hl ht]
  simp only [Nat.xor_self, Nat.zero_xor]

theorem qElt_inv
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    (qElt e l t)⁻¹ = qElt (e ^^^ par4 (l &&& t)) l t := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [qElt_mul he hl ht (xor_lt_two he (par4_lt _)) hl ht]
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  exact qElt_zero

theorem qElt_eq_mul
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    qElt e l t = qElt e l 0 * qElt 0 0 t := by
  rw [qElt_mul he hl (by norm_num) (by norm_num) (by norm_num) ht,
    par4_zero_left 0 (by norm_num)]
  simp only [Nat.xor_zero, Nat.zero_xor]

theorem qElt_inj
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) (h : qElt e l t = qElt e' l' t') :
    e = e' ∧ l = l' ∧ t = t' := by
  obtain ⟨h1, h2⟩ := mk_monomial_eq h
  have hc : affC e' l' = affC e l := by
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      have h0 := congrArg (fun c : C => (c : Fin 24 → ZMod 2) 0) h1
      simp only [Submodule.coe_add, Pi.add_apply] at h0
      rw [affC_apply_J (i := 0) he' hl' (by decide), affC_apply_J (i := 0) he hl (by decide)]
        at h0
      exact absurd h0 (by decide)
  obtain ⟨h3, h4⟩ := affC_inj he' hl' he hl hc
  exact ⟨h3.symm, h4.symm, (transP_inj ht' ht h2).symm⟩

theorem qElt_one_zero_zero :
    qElt 1 0 0 = (rK : OLq) := by
  have hc : affC 1 0 = VisQuot.ΩC + dC := by
    apply Subtype.ext
    rw [coe_affC (by norm_num) (by norm_num), Submodule.coe_add, bvec_affMask_one_zero,
      coe_dC_eq]
    rfl
  change QuotientGroup.mk (gO (affC 1 0) * PO (transP 0)) = alpha 12
  rw [hc, transP_zero, PO_one, mul_one, gO_add, gO_ΩC, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _), one_mul, alpha12_eq]

theorem mem_Agrp_iff
    {x : OLq} : x ∈ Agrp ↔ ∃ e < 2, ∃ l < 16, x = qElt e l 0 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨e, he, l, hl, h⟩ := mem_CJc_iff.1 hc
    refine ⟨e, he, l, hl, ?_⟩
    rw [qElt, transP_zero, PO_one, mul_one, show c = affC e l from Subtype.ext h]
  · rintro ⟨e, he, l, hl, rfl⟩
    refine ⟨affC e l, affC_mem_CJc he hl, ?_⟩
    rw [qElt, transP_zero, PO_one, mul_one]

theorem mem_Tgrp_iff
    {x : OLq} : x ∈ Tgrp ↔ ∃ t < 16, x = qElt 0 0 t := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_Tperm_iff.1 hp
    exact ⟨t, ht, by rw [qElt, affC_zero, gO_zero, one_mul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨transP t, transP_mem_Tperm ht, by rw [qElt, affC_zero, gO_zero, one_mul]⟩

@[expose] def Qset : Subgroup OLq where
  carrier := {x | ∃ e < 2, ∃ l < 16, ∃ t < 16, x = qElt e l t}
  one_mem' := ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, qElt_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, l, hl, t, ht, rfl⟩ ⟨e', he', l', hl', t', ht', rfl⟩
    exact ⟨_, xor_lt_two (xor_lt_two he he') (par4_lt _), _, xor_lt_sixteen hl hl', _,
      xor_lt_sixteen ht ht', qElt_mul he hl ht he' hl' ht'⟩
  inv_mem' := by
    rintro _ ⟨e, he, l, hl, t, ht, rfl⟩
    exact ⟨_, xor_lt_two he (par4_lt _), l, hl, t, ht, qElt_inv he hl ht⟩

theorem mem_Qgrp_iff
    {x : OLq} : x ∈ Qgrp ↔ ∃ e < 2, ∃ l < 16, ∃ t < 16, x = qElt e l t := by
  constructor
  · intro hx
    have hle : Qgrp ≤ Qset := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨e, he, l, hl, rfl⟩ := mem_Agrp_iff.1 hy
        exact ⟨e, he, l, hl, 0, by norm_num, rfl⟩
      · obtain ⟨t, ht, rfl⟩ := mem_Tgrp_iff.1 hy
        exact ⟨0, by norm_num, 0, by norm_num, t, ht, rfl⟩
    exact hle hx
  · rintro ⟨e, he, l, hl, t, ht, rfl⟩
    rw [qElt_eq_mul he hl ht]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_Agrp_iff.2 ⟨e, he, l, hl, rfl⟩))
      (Subgroup.mem_sup_right (mem_Tgrp_iff.2 ⟨t, ht, rfl⟩))

end CFSG.Monster.B.TwoA.Co2Inv
