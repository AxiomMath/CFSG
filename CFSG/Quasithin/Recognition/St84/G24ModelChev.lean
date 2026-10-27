module

public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts
import CFSG.Quasithin.Vol2.F134LieG2Borel
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcCore
import CFSG.Quasithin.Vol2.Ch10SecKRPb
import all CFSG.LieType.Multipliers.G24Bridge
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalParabolic
import CFSG.Quasithin.H13.NQCatExcParSq

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Fischer
open CFSG.LieType.Multipliers.G24
open CFSG.Quasithin.G2U CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open CFSG.QuasithinUnique.Setup.X6 (g2Index inf_eq_of_covBy)

private theorem toGL_injective : Function.Injective toGL :=
  (glHom_injective (RingEquiv.refl F4)).comp Subtype.val_injective

private theorem coe_adjointEquiv (y : Y) :
    ((adjointEquiv (RingEquiv.refl F4) natCard_F4 y : grp) : GL (Fin 14) F4) = toGL y := by
  unfold adjointEquiv toGL
  simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply, MonoidHom.comp_apply]
  rfl

private theorem toGL_xY (i : Fin 2) (c : F4) :
    (toGL (xY i c) : Matrix (Fin 14) (Fin 14) F4) = CFSG.Quasithin.G2U.XMat F4 (ix i) c := by
  unfold toGL xY
  rw [MonoidHom.comp_apply, glHom_apply, coe_glEquiv]
  change endEquiv (RingEquiv.refl F4) (xUnit Tag.G2 F4 (ix i) c : Module.End F4
    (RootModule Tag.G2 F4)) = CFSG.Quasithin.G2U.XMat F4 (ix i) c
  rw [coe_xUnit, endEquiv_xOp]
  rfl

private theorem toGL_yY (i : Fin 2) (c : F4) :
    (toGL (yY i c) : Matrix (Fin 14) (Fin 14) F4) = CFSG.Quasithin.G2U.YMat F4 (ix i) c := by
  unfold toGL yY
  rw [MonoidHom.comp_apply, glHom_apply, coe_glEquiv]
  change endEquiv (RingEquiv.refl F4) (yUnit Tag.G2 F4 (ix i) c : Module.End F4
    (RootModule Tag.G2 F4)) = CFSG.Quasithin.G2U.YMat F4 (ix i) c
  rw [coe_yUnit, endEquiv_yOp]
  rfl

private theorem toGL_agY (w : List (Fin 6 × Bool)) :
    (toGL (agY w) : Matrix (Fin 14) (Fin 14) F4) = toMat 14 (wordArr w) := by
  have h1 : (adjointEquiv (RingEquiv.refl F4) natCard_F4 (agY w) : grp) =
      FreeGroup.lift gen (FreeGroup.mk w) := by
    unfold agY
    exact (adjointEquiv (RingEquiv.refl F4) natCard_F4).apply_symm_apply _
  rw [← coe_adjointEquiv, h1, coe_lift_gen, val_lift_genGL]

private theorem agY_append (u v : List (Fin 6 × Bool)) : agY (u ++ v) = agY u * agY v := by
  unfold agY
  rw [← map_mul, ← map_mul, ← FreeGroup.mul_mk]

private theorem agY_invW (w : List (Fin 6 × Bool)) :
    agY (CFSG.Quasithin.St84.G24Wit.invW w) = (agY w)⁻¹ := by
  unfold agY
  rw [show CFSG.Quasithin.St84.G24Wit.invW w = FreeGroup.invRev w from by
    simp [CFSG.Quasithin.St84.G24Wit.invW, FreeGroup.invRev, List.map_reverse]]
  rw [← FreeGroup.inv_mk, map_inv, map_inv]

private theorem xY_eq_agY (i : Fin 2) (c : F4) :
    xY i c = agY (genWordX (ix i) c) := by
  apply toGL_injective
  apply Units.ext
  rw [toGL_xY, toGL_agY]
  have hr := root_check
  rw [rootCheck, List.all_eq_true] at hr
  have hic := List.all_eq_true.mp (hr (ix i) (List.mem_finRange (ix i))) c (mem_allF4 c)
  rw [Bool.and_eq_true] at hic
  rw [show wordArr (genWordX (ix i) c) = ofMat (CFSG.Quasithin.G2U.XMat F4 (ix i) c) from
    (of_decide_eq_true hic.1).symm, toMat_ofMat]

private theorem yY_eq_agY (i : Fin 2) (c : F4) :
    yY i c = agY (genWordY (ix i) c) := by
  apply toGL_injective
  apply Units.ext
  rw [toGL_yY, toGL_agY]
  have hr := root_check
  rw [rootCheck, List.all_eq_true] at hr
  have hic := List.all_eq_true.mp (hr (ix i) (List.mem_finRange (ix i))) c (mem_allF4 c)
  rw [Bool.and_eq_true] at hic
  rw [show wordArr (genWordY (ix i) c) = ofMat (CFSG.Quasithin.G2U.YMat F4 (ix i) c) from
    (of_decide_eq_true hic.2).symm, toMat_ofMat]

private theorem xY_mem_B0 (i : Fin 2) (c : F4) : xY i c ∈ B0 := by
  unfold xY B0 borelSub
  exact Subgroup.mem_subgroupOf.2 (xUnit_mem_borelGroup (ix i) c)

private theorem hY_mem_B0 (i : Fin 2) : hY i ∈ B0 := by
  unfold hY B0 borelSub
  exact Subgroup.mem_subgroupOf.2
    (torusGroup_le_borelGroup (torusElt_mem_torusGroup (ix i) omegaU))

private theorem nY_eq (i : Fin 2) : nY i = xY i 1 * yY i 1 * xY i 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [nY, xY, yY, Subtype.coe_mk, Subgroup.coe_mul, Units.val_mul,
    weylElt_eq_xUnit_mul, xUnit, yUnit, inv_one, Units.val_one, CharTwo.neg_eq]

private theorem hY_eq (i : Fin 2) :
    hY i = xY i F4.ω * yY i (F4.ω * F4.ω) * xY i F4.ω * nY i := by
  apply Subtype.ext
  apply Units.ext
  have hneg1 : (-1 : F4ˣ) = 1 := by
    ext
    rw [Units.val_neg, Units.val_one, CharTwo.neg_eq]
  have homega : F4.ω⁻¹ = F4.ω * F4.ω := rfl
  simp only [hY, torusElt, Subtype.coe_mk]
  rw [hneg1]
  simp only [nY, xY, yY, Subgroup.coe_mul, Units.val_mul, coe_torusElt,
    weylElt_eq_xUnit_mul, xUnit, yUnit, omegaU, inv_one, Units.val_one,
    Units.val_inv_eq_inv_val, homega, CharTwo.neg_eq]

private theorem T0_le_B0 : T0 ≤ B0 := posUnipotentSub_le_borelSub

private theorem B0_le_M1 : B0 ≤ M1 := by
  intro y hy
  rw [M1, Subgroup.mem_subgroupOf]
  exact borelGroup_le_parabolicSubgroup _ (Subgroup.mem_subgroupOf.1 hy)

private theorem B0_le_M2 : B0 ≤ M2 := by
  intro y hy
  rw [M2, Subgroup.mem_subgroupOf]
  exact borelGroup_le_parabolicSubgroup _ (Subgroup.mem_subgroupOf.1 hy)

private theorem nY_one_mem_M1 : nY 1 ∈ M1 := by
  rw [M1, Subgroup.mem_subgroupOf]
  change weylElt Tag.G2 F4 (ix 1) 1 ∈ parabolicSubgroup Tag.G2 F4 {g2Index 1}
  rw [show ix 1 = g2Index 1 from
    (Fin.ext rfl : ix 1 = i1).trans CFSG.Quasithin.F112R.St84.G2q.g2Index_one.symm]
  exact weylElt_mem_parabolicSubgroup (Set.mem_singleton _)

private theorem nY_zero_mem_M2 : nY 0 ∈ M2 := by
  rw [M2, Subgroup.mem_subgroupOf]
  change weylElt Tag.G2 F4 (ix 0) 1 ∈ parabolicSubgroup Tag.G2 F4 {g2Index 0}
  rw [show ix 0 = g2Index 0 from
    (Fin.ext rfl : ix 0 = i0).trans CFSG.Quasithin.F112R.St84.G2q.g2Index_zero.symm]
  exact weylElt_mem_parabolicSubgroup (Set.mem_singleton _)

private theorem closure_subgroupOf_le {S : Set (ModGL Tag.G2 F4)}
    (hSC : Subgroup.closure S ≤ adjointGroup Tag.G2 F4) {H : Subgroup Y}
    (hgen : ∀ v (hv : v ∈ S), (⟨v, hSC (Subgroup.subset_closure hv)⟩ : Y) ∈ H)
    {v : ModGL Tag.G2 F4} (hv : v ∈ Subgroup.closure S) :
    (⟨v, hSC hv⟩ : Y) ∈ H := by
  refine Subgroup.closure_induction (p := fun v hv => (⟨v, hSC hv⟩ : Y) ∈ H) ?_ ?_ ?_ ?_ hv
  · exact hgen
  · have he : (⟨1, hSC (Subgroup.one_mem _)⟩ : Y) = 1 := by
      apply Subtype.ext
      rfl
    rw [he]
    exact H.one_mem
  · intro a b ha hb haH hbH
    have he : (⟨a * b, hSC (mul_mem ha hb)⟩ : Y) =
        (⟨a, hSC ha⟩ : Y) * ⟨b, hSC hb⟩ := rfl
    rw [he]
    exact H.mul_mem haH hbH
  · intro a ha haH
    have he : (⟨a⁻¹, hSC (inv_mem ha)⟩ : Y) = (⟨a, hSC ha⟩ : Y)⁻¹ := rfl
    rw [he]
    exact H.inv_mem haH

private theorem parabolicSubgroup_subgroupOf_le {J : Set (Fin Tag.G2.rank)}
    {H : Subgroup Y} (hB : B0 ≤ H)
    (hJ : ∀ j ∈ J, (⟨weylElt Tag.G2 F4 j 1, weylElt_mem_adjointGroup j 1⟩ : Y) ∈ H) :
    (parabolicSubgroup Tag.G2 F4 J).subgroupOf (adjointGroup Tag.G2 F4) ≤ H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [parabolicSubgroup, Subgroup.sup_eq_closure] at hx
  have hIC : Subgroup.closure ((fun j => weylElt Tag.G2 F4 j 1) '' J) ≤
      adjointGroup Tag.G2 F4 := by
    rw [Subgroup.closure_le]
    rintro v ⟨j, hj, rfl⟩
    exact weylElt_mem_adjointGroup j 1
  have hclC : Subgroup.closure (((borelGroup Tag.G2 F4 : Set (ModGL Tag.G2 F4)) ∪
      ↑(Subgroup.closure ((fun j => weylElt Tag.G2 F4 j 1) '' J)))) ≤
      adjointGroup Tag.G2 F4 := by
    rw [Subgroup.closure_le]
    rintro v (hv | hv)
    · exact borelGroup_le_adjointGroup' hv
    · exact hIC hv
  have hIH : ∀ v (hv : v ∈ Subgroup.closure ((fun j => weylElt Tag.G2 F4 j 1) '' J)),
      (⟨v, hIC hv⟩ : Y) ∈ H := fun v hv =>
    closure_subgroupOf_le hIC (fun w hw => by
      rcases hw with ⟨j, hj, rfl⟩
      exact hJ j hj) hv
  have hxH : (⟨(x : ModGL Tag.G2 F4), hclC hx⟩ : Y) ∈ H :=
    closure_subgroupOf_le hclC (fun v hv => by
      rcases hv with hv | hv
      · exact hB (Subgroup.mem_subgroupOf.2 hv)
      · exact hIH v hv) hx
  simpa using hxH

private theorem M1_le_of {H : Subgroup Y} (hB : B0 ≤ H) (hn : nY 1 ∈ H) : M1 ≤ H := by
  refine parabolicSubgroup_subgroupOf_le (J := {g2Index 1}) hB ?_
  intro j hj
  rw [Set.mem_singleton_iff] at hj
  subst hj
  have h : (⟨weylElt Tag.G2 F4 (g2Index 1) 1, weylElt_mem_adjointGroup _ _⟩ : Y) = nY 1 := by
    apply Subtype.ext
    unfold nY
    rw [show g2Index 1 = ix 1 from
      ((Fin.ext rfl : ix 1 = i1).trans CFSG.Quasithin.F112R.St84.G2q.g2Index_one.symm).symm]
  rw [h]
  exact hn

private theorem M2_le_of {H : Subgroup Y} (hB : B0 ≤ H) (hn : nY 0 ∈ H) : M2 ≤ H := by
  refine parabolicSubgroup_subgroupOf_le (J := {g2Index 0}) hB ?_
  intro j hj
  rw [Set.mem_singleton_iff] at hj
  subst hj
  have h : (⟨weylElt Tag.G2 F4 (g2Index 0) 1, weylElt_mem_adjointGroup _ _⟩ : Y) = nY 0 := by
    apply Subtype.ext
    unfold nY
    rw [show g2Index 0 = ix 0 from
      ((Fin.ext rfl : ix 0 = i0).trans CFSG.Quasithin.F112R.St84.G2q.g2Index_zero.symm).symm]
  rw [h]
  exact hn

private theorem inf_M1_M2 : M1 ⊓ M2 = B0 := CFSG.Quasithin.F112R.St84.G2q.g2ParA_inf_g2ParB

private theorem normalizer_T0 : Subgroup.normalizer (T0 : Set Y) = B0 :=
  CFSG.Quasithin.F112R.St84.G2q.normalizer_posUnipotentSub.trans
    CFSG.Quasithin.F112R.St84.G2q.g2ParA_inf_g2ParB

private theorem card_T0 : Nat.card T0 = 4096 := by
  rw [T0, card_subgroupOf_of_le posUnipotent_le_adjointGroup, card_posUnipotent,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2, natCard_F4]
  norm_num

private theorem card_B0 : Nat.card B0 = 36864 := by
  rw [B0, card_subgroupOf_of_le (borelGroup_le_adjointGroup' (τ := Tag.G2) (K := F4)),
    card_borelGroup, CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, card_posUnipotent,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2, natCard_F4]
  norm_num

private theorem card_M1 : Nat.card M1 = 184320 := by
  rw [M1, card_subgroupOf_of_le (parabolicSubgroup_le_adjointGroup Tag.G2 F4 _),
    CFSG.Quasithin.F134.LieG2.card_parabolicSubgroup_singleton,
    card_borelGroup, CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, card_posUnipotent,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2, natCard_F4]
  norm_num

private theorem card_M2 : Nat.card M2 = 184320 := by
  rw [M2, card_subgroupOf_of_le (parabolicSubgroup_le_adjointGroup Tag.G2 F4 _),
    CFSG.Quasithin.F134.LieG2.card_parabolicSubgroup_singleton,
    card_borelGroup, CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, card_posUnipotent,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2, natCard_F4]
  norm_num

private theorem isPGroup_T0 : IsPGroup 2 T0 := by
  have hU : IsPGroup 2 (posUnipotent Tag.G2 F4) := isPGroup_posUnipotent 2 Tag.G2
  exact hU.comap_of_injective (adjointGroup Tag.G2 F4).subtype Subtype.coe_injective

private theorem isSylowTwoOf_T0_M1 : CFSG.QuasithinUnique.IsSylowTwoOf T0 M1 := by
  refine ⟨T0_le_B0.trans B0_le_M1, isPGroup_T0, ?_⟩
  have hcard : Nat.card (T0.subgroupOf M1) = 4096 := by
    rw [card_subgroupOf_of_le (T0_le_B0.trans B0_le_M1), card_T0]
  have h := (T0.subgroupOf M1).card_mul_index
  rw [hcard, card_M1] at h
  have hidx : (T0.subgroupOf M1).index = 45 := by omega
  rw [hidx]
  norm_num

private theorem isSylowTwoOf_T0_M2 : CFSG.QuasithinUnique.IsSylowTwoOf T0 M2 := by
  refine ⟨T0_le_B0.trans B0_le_M2, isPGroup_T0, ?_⟩
  have hcard : Nat.card (T0.subgroupOf M2) = 4096 := by
    rw [card_subgroupOf_of_le (T0_le_B0.trans B0_le_M2), card_T0]
  have h := (T0.subgroupOf M2).card_mul_index
  rw [hcard, card_M2] at h
  have hidx : (T0.subgroupOf M2).index = 45 := by omega
  rw [hidx]
  norm_num

private theorem le_T0_of_isPGroup {N : Subgroup Y} (hN : N ≤ B0) (hp : IsPGroup 2 N) : N ≤ T0 := by
  have hPN : (T0.subgroupOf B0).Normal := normal_posUnipotentSub
  have hcardP : Nat.card (T0.subgroupOf B0) = 4096 := by
    rw [card_subgroupOf_of_le T0_le_B0, card_T0]
  have hidx : (T0.subgroupOf B0).index = 9 := by
    have h := (T0.subgroupOf B0).card_mul_index
    rw [hcardP, card_B0] at h
    omega
  have hodd : Odd (T0.subgroupOf B0).index := by rw [hidx]; norm_num
  have hp' : IsPGroup 2 (N.subgroupOf B0) :=
    hp.comap_of_injective B0.subtype Subtype.coe_injective
  have hle := CFSG.GorensteinWalter.subgroup_le_of_isPGroup_coindex_odd
    (T0.subgroupOf B0) hPN hodd (N.subgroupOf B0) hp'
  intro x hx
  have hxB : x ∈ B0 := hN hx
  have hx' : (⟨x, hxB⟩ : ↥B0) ∈ T0.subgroupOf B0 := hle (by
    rw [Subgroup.mem_subgroupOf]; exact hx)
  rwa [Subgroup.mem_subgroupOf] at hx'

private theorem card_pCoreOf_M1 : Nat.card (CFSG.Open.pCoreOf 2 M1) = 1024 := by
  change Nat.card (CFSG.Open.pCoreOf 2
    ((parabolicSubgroup Tag.G2 F4 {g2Index 1}).subgroupOf
      (adjointGroup Tag.G2 F4))) = 1024
  rw [← Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (adjointGroup Tag.G2 F4)),
    CFSG.Quasithin.Vol2.Ch10.SecB.KRP.map_pCoreOf_subgroupOf
      (parabolicSubgroup_le_adjointGroup Tag.G2 F4 {g2Index 1}),
    CFSG.StandardType.GGOppRadExc.pCoreOf_parabolicSubgroup,
    card_parabolicRadical, CFSG.Quasithin.H13.NQCat.ExcParSq.ncard_radicalRoots_g2,
    natCard_F4]
  norm_num

private theorem card_pCoreOf_M2 : Nat.card (CFSG.Open.pCoreOf 2 M2) = 1024 := by
  change Nat.card (CFSG.Open.pCoreOf 2
    ((parabolicSubgroup Tag.G2 F4 {g2Index 0}).subgroupOf
      (adjointGroup Tag.G2 F4))) = 1024
  rw [← Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (adjointGroup Tag.G2 F4)),
    CFSG.Quasithin.Vol2.Ch10.SecB.KRP.map_pCoreOf_subgroupOf
      (parabolicSubgroup_le_adjointGroup Tag.G2 F4 {g2Index 0}),
    CFSG.StandardType.GGOppRadExc.pCoreOf_parabolicSubgroup,
    card_parabolicRadical, CFSG.Quasithin.H13.NQCat.ExcParSq.ncard_radicalRoots_g2,
    natCard_F4]
  norm_num

theorem chevFacts : ChevFacts where
  toGL_injective := toGL_injective
  toGL_agY := toGL_agY
  agY_append := agY_append
  agY_invW := agY_invW
  xY_eq_agY := xY_eq_agY
  yY_eq_agY := yY_eq_agY
  nY_eq := nY_eq
  hY_eq := hY_eq
  xY_mem_B0 := xY_mem_B0
  hY_mem_B0 := hY_mem_B0
  nY_one_mem_M1 := nY_one_mem_M1
  nY_zero_mem_M2 := nY_zero_mem_M2
  T0_le_B0 := T0_le_B0
  B0_le_M1 := B0_le_M1
  B0_le_M2 := B0_le_M2
  M1_le_of := M1_le_of
  M2_le_of := M2_le_of
  inf_M1_M2 := inf_M1_M2
  normalizer_T0 := normalizer_T0
  card_T0 := card_T0
  card_B0 := card_B0
  le_T0_of_isPGroup := le_T0_of_isPGroup
  isSylowTwoOf_T0_M1 := isSylowTwoOf_T0_M1
  isSylowTwoOf_T0_M2 := isSylowTwoOf_T0_M2
  card_pCoreOf_M1 := card_pCoreOf_M1
  card_pCoreOf_M2 := card_pCoreOf_M2

end CFSG.Quasithin.F112R.St84.G24M
