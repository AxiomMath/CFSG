
module

public import CFSG.Monster.B.TwoA.Co2Inv.CentOrderBase

public import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCert
public import CFSG.Monster.B.TwoA.Co2Inv.Mr

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

attribute [local instance] wLeftAction

theorem wAct_rK' :
    wAct v0 rK = rowsEnd (gRows 12) := wAct_rK

theorem rK_ne_one :
    rK ≠ 1 := by
  intro h
  have e := LinearMap.congr_fun (congrArg (wAct v0) h) (qbW ⟨1, by norm_num⟩)
  rw [wAct_rK', rowsEnd_qbW, wAct_one, Module.End.one_apply, ← decW_one_shiftLeft] at e
  have h1 : (gRows 12)[((⟨1, by norm_num⟩ : Fin 22) : ℕ)]! = 12317 := gRows12_one
  rw [h1] at e
  exact absurd (decW_injective (by norm_num) (by decide) e) (by decide)

theorem rK_mul_self :
    rK * rK = 1 := by
  apply eq_of_wAct_eq
  rw [wAct_mul, wAct_rK', rowsEnd_mul, gRows12_sq, rowsEnd_idRows, wAct_one]

theorem cGen_comm
    (k : Fin 21) : cGen k * rK = rK * cGen k := by
  apply eq_of_wAct_eq
  rw [wAct_mul, wAct_mul, wAct_cGen, wAct_rK', rowsEnd_mul, rowsEnd_mul, cRows_comm k k.2]

theorem cGen_mem_Cr
    (k : Fin 21) : cGen k ∈ Cr :=
  Subgroup.mem_centralizer_singleton_iff.2 (cGen_comm k)

theorem cGen_mem_Mfr
    {k : Fin 21} (hk : (k : ℕ) < 20) : cGen k ∈ Mfr := by
  change wAct v0 (cGen k) wFr = wFr
  rw [wFr_eq_decW, wAct_cGen, rowsEnd_decW, cRows_fix_w k hk]

theorem mem_Mr'
    {k : Kstab v0} : k ∈ Mr ↔ k ∈ Mfr ∧ k ∈ Cr := Subgroup.mem_inf

theorem G21_le_Cr :
    G21 ≤ Cr := by
  rw [G21_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact cGen_mem_Cr k

@[expose] def M20 :

    Subgroup (Kstab v0) := Subgroup.closure (cGen '' {k | (k : ℕ) < 20})

theorem M20_le_Mr :
    M20 ≤ Mr := by
  rw [M20, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_Mr'.2 ⟨cGen_mem_Mfr hk, cGen_mem_Cr k⟩

theorem M20_le_G21 :
    M20 ≤ G21 := by
  rw [M20, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact cGen_mem_G21 k

theorem cGen_mem_M20
    {k : Fin 21} (hk : (k : ℕ) < 20) : cGen k ∈ M20 :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

@[expose] def M20q :
    Subgroup OLq := M20.map (Kstab v0).subtype

instance finite_M20q :
    Finite M20q :=
  Finite.of_equiv _ (M20.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv

theorem fK_mem_M20q
    (k : Fin 9) : (QuotientGroup.mk (PO (fAut k)) : OLq) ∈ M20q := by
  refine ⟨cGen ⟨k, by omega⟩, cGen_mem_M20 (show (k : ℕ) < 20 by omega), ?_⟩
  rw [cGen_of_lt (show (k : ℕ) < 9 from k.2)]
  rfl

@[expose] def F9A :
    Subgroup AutPerm := Subgroup.closure (Set.range fAut)

theorem PO_mem_M20q
    {p : AutPerm} (hp : p ∈ Subgroup.closure (Set.range fAut)) :
    (QuotientGroup.mk (PO p) : OLq) ∈ M20q := by
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact fK_mem_M20q k
  | one =>
    rw [PO_one, QuotientGroup.mk_one]
    exact M20q.one_mem
  | mul x y _ _ hx hy =>
    rw [PO_mul, QuotientGroup.mk_mul]
    exact M20q.mul_mem hy hx
  | inv x _ hx =>
    rw [PO_inv, QuotientGroup.mk_inv]
    exact M20q.inv_mem hx

theorem F9A_le_Ppair : F9A ≤ Ppair := by
  rw [F9A, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact fAut_mem_Ppair k

theorem F9A_le_Foct : F9A ≤ Foct := by
  rw [F9A, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine mem_Foct.2 ⟨fAut_mem_Ppair k, fun i => ?_⟩
  have h := fPerms_octad k k.2 i i.2
  rw [← fAut_apply k i] at h
  exact h

theorem f9Hyp : MonoHyp Ceq F9A :=
  ⟨ceqHyp.le_C, ceqHyp.Ω_mem, fun p hp a ha => ceqHyp.preserves p (F9A_le_Ppair hp) a ha⟩

theorem map_F9A : F9A.map AutPerm.subtype = F9 := by
  rw [F9A, MonoidHom.map_closure, F9]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨⟨k, hk⟩, rfl⟩, rfl⟩

theorem natCard_F9A :
    Nat.card F9A = 11520 := by
  rw [← natCard_F9, ← map_F9A, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

theorem gO_mem_M20q_aux :

    ∀ x ∈ Submodule.span (ZMod 2) (Set.range signVec), ∀ hx : x ∈ C,
    (QuotientGroup.mk (gO ⟨x, hx⟩) : OLq) ∈ M20q := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro hxC
    obtain ⟨j, rfl⟩ := hx
    have e : (⟨signVec j, hxC⟩ : C) = wordC (genRecord ⟨12 + j, by omega⟩).word :=
      Subtype.ext (wordC_eq_bvec j).symm
    rw [e, ← alpha_sign j]
    refine ⟨cGen ⟨9 + j, by omega⟩, cGen_mem_M20 (show 9 + (j : ℕ) < 20 by omega), ?_⟩
    rw [cGen_of_ge (show 9 ≤ 9 + (j : ℕ) by omega)]
    change alpha _ = alpha _
    exact congrArg alpha (Fin.ext (show 9 + (j : ℕ) + 3 = 12 + (j : ℕ) by omega))
  | zero =>
    intro h0
    rw [show (⟨0, h0⟩ : C) = 0 from rfl, gO_zero, QuotientGroup.mk_one]
    exact M20q.one_mem
  | add x y hx hy ihx ihy =>
    intro hxy
    have hx' : x ∈ C := ceqHyp.le_C (show x ∈ Ceq by rw [← span_signVec]; exact hx)
    have hy' : y ∈ C := ceqHyp.le_C (show y ∈ Ceq by rw [← span_signVec]; exact hy)
    rw [show (⟨x + y, hxy⟩ : C) = ⟨x, hx'⟩ + ⟨y, hy'⟩ from rfl, gO_add, QuotientGroup.mk_mul]
    exact M20q.mul_mem (ihx hx') (ihy hy')
  | smul t x hx ihx =>
    intro htx
    have hx' : x ∈ C := ceqHyp.le_C (show x ∈ Ceq by rw [← span_signVec]; exact hx)
    rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) t with rfl | rfl
    · rw [show (⟨(0 : ZMod 2) • x, htx⟩ : C) = 0 from Subtype.ext (zero_smul _ _), gO_zero,
        QuotientGroup.mk_one]
      exact M20q.one_mem
    · rw [show (⟨(1 : ZMod 2) • x, htx⟩ : C) = ⟨x, hx'⟩ from Subtype.ext (one_smul _ _)]
      exact ihx hx'

theorem gO_mem_M20q
    {c : C} (hc : (c : Fin 24 → ZMod 2) ∈ Ceq) :
    (QuotientGroup.mk (gO c) : OLq) ∈ M20q := by
  rw [← span_signVec] at hc
  exact gO_mem_M20q_aux _ hc c.2

theorem monoSub_f9_le :
    monoSub f9Hyp ≤ M20q := by
  intro x hx
  obtain ⟨a, ha, p, hp, rfl⟩ := (mem_monoSub_iff f9Hyp).1 hx
  rw [QuotientGroup.mk_mul]
  exact M20q.mul_mem (gO_mem_M20q ha) (PO_mem_M20q hp)

theorem natCard_M20_ge :
    11796480 ≤ Nat.card M20 := by
  have h1 := Subgroup.card_le_of_le monoSub_f9_le
  rw [natCard_monoSub, natCard_quot_ΩIn f9Hyp, finrank_Ceq, natCard_F9A, M20q,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
  exact (show (11796480 : ℕ) = 2 ^ (11 - 1) * 11520 by norm_num).trans_le h1

theorem natCard_G21_eq :
    Nat.card G21 = 63 * Nat.card (MulAction.stabilizer G21 wFr) := by
  rw [← (MulAction.stabilizer G21 wFr).index_mul_card, MulAction.index_stabilizer,
    ncard_orbit_G21_wFr]

theorem M20_le_stab :
    M20.subgroupOf G21 ≤ MulAction.stabilizer G21 wFr := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  change wAct v0 ((g : Kstab v0)⁻¹) wFr = wFr
  exact (mem_Mr'.1 (M20_le_Mr (M20.inv_mem (Subgroup.mem_subgroupOf.1 hg)))).1

theorem natCard_M20_le_stab :
    Nat.card M20 ≤ Nat.card (MulAction.stabilizer G21 wFr) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe M20_le_G21).toEquiv]
  exact Subgroup.card_le_of_le M20_le_stab

theorem G21_eq_Cr :
    G21 = Cr := by
  refine Subgroup.eq_of_le_of_card_ge G21_le_Cr ?_
  rw [natCard_Cr, natCard_G21_eq]
  have := natCard_M20_le_stab
  have := natCard_M20_ge
  omega

theorem natCard_G21 :
    Nat.card G21 = 743178240 := by rw [G21_eq_Cr, natCard_Cr]

theorem natCard_stab_G21 :
    Nat.card (MulAction.stabilizer G21 wFr) = 11796480 := by
  have h := natCard_G21_eq
  rw [natCard_G21] at h
  omega

theorem M20_eq_Mr :
    M20 = Mr ∧ Nat.card Mr = 11796480 := by
  have hle : Mr.subgroupOf G21 ≤ MulAction.stabilizer G21 wFr := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    change wAct v0 ((g : Kstab v0)⁻¹) wFr = wFr
    exact (mem_Mr'.1 (Mr.inv_mem (Subgroup.mem_subgroupOf.1 hg))).1
  have hMr : Mr ≤ G21 := fun k hk => by
    rw [G21_eq_Cr]
    exact (mem_Mr'.1 hk).2
  have h1 : Nat.card Mr ≤ 11796480 := by
    rw [← natCard_stab_G21, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMr).toEquiv]
    exact Subgroup.card_le_of_le hle
  have h2 := Subgroup.card_le_of_le M20_le_Mr
  have h3 := natCard_M20_ge
  exact ⟨Subgroup.eq_of_le_of_card_ge M20_le_Mr (by omega), by omega⟩

theorem natCard_Foct :
    Nat.card Foct = 11520 ∧ F9A = Foct := by
  have h := natCard_Mr
  rw [M20_eq_Mr.2] at h
  have hF : Nat.card Foct = 11520 := by
    norm_num at h
    omega
  refine ⟨hF, Subgroup.eq_of_le_of_card_ge F9A_le_Foct ?_⟩
  rw [hF, natCard_F9A]

@[expose] def Hgrp :
    Subgroup (Kstab v0) := Subgroup.closure (insert aK (Mr : Set (Kstab v0)))

theorem aK_eq :
    aK = cGen 20 := by
  rw [cGen_of_ge (by simp)]
  rfl

theorem Hgrp_eq_Cr :
    Hgrp = Cr := by
  apply le_antisymm
  · rw [Hgrp, Subgroup.closure_le]
    rintro _ (rfl | h)
    · rw [aK_eq]
      exact cGen_mem_Cr 20
    · exact (mem_Mr'.1 h).2
  · rw [← G21_eq_Cr, G21_eq, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : (k : ℕ) < 20
    · refine Subgroup.subset_closure (Set.mem_insert_of_mem _ ?_)
      rw [← M20_eq_Mr.1]
      exact cGen_mem_M20 hk
    · have : k = 20 := by omega
      rw [this, ← aK_eq]
      exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem orbit_Cr_wFr :
    {x | ∃ k ∈ Cr, wAct v0 k wFr = x} =
    (fun i => decW frameOrbit[i]!) '' {i | i < 63} := by
  rw [← (show frameOrbit.size = 63 from rfl), ← orbit_G21_wFr]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [← G21_eq_Cr] at hk
    refine ⟨⟨k⁻¹, G21.inv_mem hk⟩, ?_⟩
    change wAct v0 (k⁻¹)⁻¹ wFr = wAct v0 k wFr
    rw [inv_inv]
  · rintro ⟨g, rfl⟩
    refine ⟨(g : Kstab v0)⁻¹, ?_, rfl⟩
    rw [← G21_eq_Cr]
    exact G21.inv_mem g.2

theorem native_Co2_central_involution_centralizer_order :
    supp ((dC : C) : Fin 24 → ZMod 2) = Finset.univ.filter (fun i : Fin 24 => (i : ℕ) < 8) ∧
    (rK : OLq) = alpha 12 ∧ alpha 12 = QuotientGroup.mk (gO dC) ∧
    (aK : OLq) = alpha 23 ∧ alpha 23 = QuotientGroup.mk (xiO * gO (bC 0)) ∧
    rK ≠ 1 ∧ orderOf rK = 2 ∧ (conjugatesOf rK).ncard = 56925 ∧
    Hgrp = Cr ∧ Nat.card Cr = 743178240 ∧
    Nat.card Foct = 11520 ∧ Subgroup.closure (Set.range fAut) = Foct ∧
    (∀ k : Fin 9, ∀ i : Fin 24,
      (((fAut k : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) = (fPerms[(k : ℕ)]!)[(i : ℕ)]!) ∧
    (∀ k : Kstab v0, k ∈ Mr ↔ ∃ c : C, (c : Fin 24 → ZMod 2) ∈ Ceq ∧ ∃ p ∈ Foct,
      (k : OLq) = QuotientGroup.mk (gO c * PO p)) ∧
    Nonempty (SDD foctHyp ≃* Mr) ∧ Nat.card Mr = 11796480 ∧
    Subgroup.closure (Set.range cGen) = Cr ∧
    (∀ k : Fin 21, wAct v0 (cGen k) = rowsEnd candRows[(k : ℕ)]!) ∧
    (∀ k : Fin 21, ∀ hk : (k : ℕ) < 9,
      (cGen k : OLq) = QuotientGroup.mk (PO (fAut ⟨k, hk⟩))) ∧
    (∀ k : Fin 21, ∀ hk : 9 ≤ (k : ℕ), (cGen k : OLq) = alpha ⟨k + 3, by omega⟩) ∧
    cGen 20 = aK ∧
    {x | ∃ k ∈ Cr, wAct v0 k wFr = x} = (fun i => decW frameOrbit[i]!) '' {i | i < 63} := by
  refine ⟨supp_dC, rfl, alpha12_eq, rfl, alpha23_eq, rK_ne_one, ?_, ncard_conjClass_rK,
    Hgrp_eq_Cr, natCard_Cr, natCard_Foct.1, natCard_Foct.2, fAut_apply,
    fun k => (mem_Mr_iff k).trans (mem_monoSub_iff foctHyp), ⟨MrEquiv⟩, M20_eq_Mr.2, ?_,
    fun k => ?_, fun k hk => ?_, fun k hk => ?_, aK_eq.symm, orbit_Cr_wFr⟩
  · exact orderOf_eq_prime (by rw [sq]; exact rK_mul_self) rK_ne_one
  · rw [← G21_eq, G21_eq_Cr]
  · rw [wAct_cGen, cRows_eq_candRows k k.2]
  · rw [cGen_of_lt hk]
    rfl
  · rw [cGen_of_ge hk]

end CFSG.Monster.B.TwoA.Co2Inv
