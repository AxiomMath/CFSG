module

import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Unitary.CliqueKernel
public import Mathlib.Tactic.Have

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix
open scoped LinearAlgebra.Projectivization

@[expose] def hermL (y : V) : V →ₗ[F4] F4 where
  toFun v := herm v y
  map_add' a b := herm_add_left a b y
  map_smul' c v := herm_smul_left c v y

@[expose] noncomputable def perpSub (p : IsoPt) : Submodule F4 V := LinearMap.ker (hermL p.1.rep)

theorem mem_perpSub {p : IsoPt} {v : V} : v ∈ perpSub p ↔ herm v p.1.rep = 0 := Iff.rfl

theorem submodule_eq_span (p : IsoPt) : p.1.submodule = Submodule.span F4 {p.1.rep} := by
  conv_lhs => rw [← Projectivization.mk_rep p.1]
  exact Projectivization.submodule_mk _ _

theorem mem_perpSub_iff {p : IsoPt} {v : V} :
    v ∈ perpSub p ↔ ∀ w ∈ p.1.submodule, herm v w = 0 := by
  rw [mem_perpSub, submodule_eq_span]
  constructor
  · intro h w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [herm_smul_right, h, mul_zero]
  · intro h
    exact h _ (Submodule.mem_span_singleton_self _)

@[expose] def fiberY (W A : Submodule F4 V) : Set IsoPt :=
  {p | p ∉ planePts W ∧ perpSub p ⊓ W = A}

theorem mem_fiberY {W A : Submodule F4 V} {p : IsoPt} :
    p ∈ fiberY W A ↔ p ∉ planePts W ∧ perpSub p ⊓ W = A := Iff.rfl

@[expose] noncomputable def fixL (p : IsoPt) : Subgroup ProjSU :=
  (MulAction.stabilizer (Equiv.Perm IsoPt) p).comap projAct

theorem mem_fixL {p : IsoPt} {x : ProjSU} : x ∈ fixL p ↔ projAct x p = p := Iff.rfl

theorem finrank_perpSub_inf {W : Submodule F4 V} (hW : IsMaxIso W) {p : IsoPt}
    (hp : p ∉ planePts W) : Module.finrank F4 ↥(perpSub p ⊓ W) = 2 := by
  let f : W →ₗ[F4] F4 := (hermL p.1.rep).domRestrict W
  have hker : (LinearMap.ker f).map W.subtype = perpSub p ⊓ W := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.2⟩
    · rintro ⟨hv, hvW⟩
      exact ⟨⟨v, hvW⟩, hv, rfl⟩
  have hf : f ≠ 0 := by
    intro h0
    apply hp
    refine hW.mem_of_herm fun w hw => ?_
    have h1 : herm w p.1.rep = 0 := LinearMap.congr_fun h0 ⟨w, hw⟩
    exact herm_eq_zero_comm h1
  have hr : Module.finrank F4 (LinearMap.range f) = 1 := by
    have h1 : LinearMap.range f ≠ ⊥ := fun h => hf (LinearMap.range_eq_bot.1 h)
    have h2 := Submodule.finrank_le (LinearMap.range f)
    rw [Module.finrank_self] at h2
    have h3 : Module.finrank F4 (LinearMap.range f) ≠ 0 := fun h =>
      h1 (Submodule.finrank_eq_zero.1 h)
    omega
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hW.1] at hsum
  rw [← hker, Submodule.finrank_map_subtype_eq]
  omega

theorem orth_projAct (x : ProjSU) (a b : IsoPt) :
    Orth (projAct x a).1 (projAct x b).1 ↔ Orth a.1 b.1 := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [projAct_mk, projAct_mk, SubMulAction.val_smul, SubMulAction.val_smul]
    exact orth_smul_iff g a.1 b.1

theorem orth_pt_left {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) (b : IsoPt) :
    Orth (pt v hv0 hv).1 b.1 ↔ herm v b.1.rep = 0 := by
  have h := orth_pt hv0 b.1.rep_nonzero hv (isIsoPt_of b)
  rwa [pt_rep] at h

theorem herm_eq_zero_iff_comm {v w : V} : herm v w = 0 ↔ herm w v = 0 :=
  ⟨herm_eq_zero_comm, herm_eq_zero_comm⟩

theorem perpSub_inf_projAct {W : Submodule F4 V} (hW : IsTotIso W) {x : ProjSU} (hx : x ∈ kerL W)
    (p : IsoPt) : perpSub (projAct x p) ⊓ W = perpSub p ⊓ W := by
  ext v
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_perpSub, mem_perpSub]
  refine and_congr_left fun hvW => ?_
  by_cases hv0 : v = 0
  · rw [hv0, herm_zero_left, herm_zero_left]
  have hvi : herm v v = 0 := hW v hvW v hvW
  have hq : pt v hv0 hvi ∈ planePts W := (pt_mem_planePts hv0 hvi).2 hvW
  rw [← orth_pt_left hv0 hvi, ← orth_pt_left hv0 hvi]
  conv_rhs => rw [← orth_projAct x]
  rw [hx _ hq]

theorem projAct_mem_fiberY {W A : Submodule F4 V} (hW : IsTotIso W) {x : ProjSU}
    (hx : x ∈ kerL W) {p : IsoPt} (hp : p ∈ fiberY W A) : projAct x p ∈ fiberY W A :=
  ⟨fun h => hp.1 (((kerL_le_stabL W hx) p).1 h), by rw [perpSub_inf_projAct hW hx p, hp.2]⟩

theorem adj_iff_of_mem_fiberY {W A : Submodule F4 V} {p : IsoPt} (hp : p ∈ fiberY W A)
    {q : IsoPt} (hq : q ∈ planePts W) : isoGraph.Adj p q ↔ q ∈ planePts A := by
  have hne : p ≠ q := fun h => hp.1 (h ▸ hq)
  rw [isoGraph_adj, and_iff_right hne, orth_rep_iff, herm_eq_zero_iff_comm, mem_planePts,
    ← hp.2, Submodule.mem_inf, mem_perpSub, and_iff_left (show q.1.rep ∈ W from hq)]

theorem projAct_tPt_eq_of_herm {q r : IsoPt} (h : herm r.1.rep q.1.rep = 0) :
    projAct (tPt q) r = r := by
  rw [tPt, projAct_mk]
  conv_lhs => rw [← pt_rep r]
  rw [smul_pt]
  conv_rhs => rw [← pt_rep r]
  congr 1
  rw [smul_def, coe_transvec, transvecMat_mulVec, h, zero_smul, add_zero]

theorem tPt_mem_kerL {W : Submodule F4 V} (hW : IsTotIso W) {q : IsoPt} (hq : q ∈ planePts W) :
    tPt q ∈ kerL W :=
  fun _ hr => projAct_tPt_eq_of_herm (hW _ hr _ hq)

theorem tPt_mem_fixL {W A : Submodule F4 V} {p : IsoPt} (hp : p ∈ fiberY W A) {q : IsoPt}
    (hq : q ∈ planePts A) : tPt q ∈ fixL p := by
  refine projAct_tPt_eq_of_herm (herm_eq_zero_comm ?_)
  rw [← hp.2] at hq
  exact (Submodule.mem_inf.1 hq).1

theorem closure_le_kerL_inf_fixL {W A : Submodule F4 V} (hW : IsTotIso W) (hAW : A ≤ W)
    {p : IsoPt} (hp : p ∈ fiberY W A) :
    Subgroup.closure (tPt '' planePts A) ≤ kerL W ⊓ fixL p := by
  rw [Subgroup.closure_le]
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨tPt_mem_kerL hW (planePts_mono hAW hq), tPt_mem_fixL hp hq⟩

theorem mem_fiberY_W0_A0 {p : IsoPt} :
    p ∈ fiberY W0 A0 ↔ p.1.rep 4 = 0 ∧ p.1.rep 5 = 0 ∧ p.1.rep 3 ≠ 0 := by
  constructor
  · rintro ⟨hpW, hpA⟩
    have hu : ∀ i : Fin 6, u i ∈ A0 → herm (u i) p.1.rep = 0 := fun i hi => by
      rw [← hpA] at hi
      exact (Submodule.mem_inf.1 hi).1
    have h0 := hu 0 (by rw [mem_A0_iff]; decide)
    have h1 := hu 1 (by rw [mem_A0_iff]; decide)
    rw [herm_single_left, bar_eq_zero_iff] at h0 h1
    refine ⟨h1, h0, fun h3 => hpW ?_⟩
    exact mem_W0_iff.2 ⟨h3, h1, h0⟩
  · rintro ⟨h4, h5, h3⟩
    refine ⟨fun h => h3 (mem_W0_iff.1 h).1, ?_⟩
    ext v
    rw [Submodule.mem_inf, mem_perpSub, mem_W0_iff, mem_A0_iff]
    constructor
    · rintro ⟨hv, hv3, hv4, hv5⟩
      rw [herm_expand, h4, h5, hv3, hv4, hv5] at hv
      simp only [bar_zero, mul_zero, zero_mul, zero_add, add_zero] at hv
      refine ⟨(mul_eq_zero.1 hv).resolve_right (fun h => h3 (bar_eq_zero_iff.1 h)), hv3, hv4,
        hv5⟩
    · rintro ⟨hv2, hv3, hv4, hv5⟩
      refine ⟨?_, hv3, hv4, hv5⟩
      rw [herm_expand, h4, h5, hv2, hv3, hv4, hv5]
      simp

theorem card_fiber_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧ (v 4 = 0 ∧ v 5 = 0 ∧ v 3 ≠ 0)} = 96 := by
  decide +kernel

theorem card_A0_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧ (v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0)} =
      15 := by
  decide +kernel

theorem ncard_fiberY_W0_A0 : (fiberY W0 A0).ncard = 32 := by
  have h := card_vec_eq_three_mul (fun v : V => v 4 = 0 ∧ v 5 = 0 ∧ v 3 ≠ 0)
    (fun c v hc => by simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or, ne_eq])
  rw [card_fiber_vec] at h
  have e : fiberY W0 A0 = {p : IsoPt | p.1.rep 4 = 0 ∧ p.1.rep 5 = 0 ∧ p.1.rep 3 ≠ 0} := by
    ext p
    exact mem_fiberY_W0_A0
  rw [e, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  change Fintype.card {p : IsoPt // p.1.rep 4 = 0 ∧ p.1.rep 5 = 0 ∧ p.1.rep 3 ≠ 0} = 32
  omega

theorem ncard_planePts_A0 : (planePts A0).ncard = 5 := by
  have h := card_vec_eq_three_mul (fun v : V => v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0)
    (fun c v hc => by simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or])
  rw [card_A0_vec] at h
  have e : planePts A0 = {p : IsoPt | p.1.rep 2 = 0 ∧ p.1.rep 3 = 0 ∧ p.1.rep 4 = 0 ∧
      p.1.rep 5 = 0} := by
    ext p
    exact mem_A0_iff
  rw [e, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  change Fintype.card {p : IsoPt // p.1.rep 2 = 0 ∧ p.1.rep 3 = 0 ∧ p.1.rep 4 = 0 ∧
    p.1.rep 5 = 0} = 5
  omega

theorem herm_ofHyp_e3 (a : Fin 3 → F4) :
    herm (ofHyp a (e3 2)) (ofHyp a (e3 2)) = a 2 + bar (a 2) := by
  rw [herm_ofHyp, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [bar_one, bar_zero]

theorem bar_eq_of_add_eq_zero : ∀ x : F4, x + bar x = 0 → bar x = x := by decide

theorem add_bar_eq_zero : ∀ x : F4, bar x = x → x + bar x = 0 := by decide

theorem ofHyp_e3_ne_zero (a : Fin 3 → F4) : ofHyp a (e3 2) ≠ 0 := by
  rw [Ne, ofHyp_eq_zero_iff, not_and_or]
  right
  intro h
  have := congrFun h 2
  simp at this

@[expose] noncomputable def ptA (a : Fin 3 → F4) (ha : bar (a 2) = a 2) : IsoPt :=
  pt (ofHyp a (e3 2)) (ofHyp_e3_ne_zero a) (by rw [herm_ofHyp_e3]; exact add_bar_eq_zero _ ha)

theorem ptA_mem_fiberY (a : Fin 3 → F4) (ha : bar (a 2) = a 2) : ptA a ha ∈ fiberY W0 A0 := by
  rw [mem_fiberY_W0_A0]
  obtain ⟨c, hc⟩ := rep_pt (ofHyp_e3_ne_zero a)
    (by rw [herm_ofHyp_e3]; exact add_bar_eq_zero _ ha)
  change (pt _ _ _).1.rep 4 = 0 ∧ (pt _ _ _).1.rep 5 = 0 ∧ (pt _ _ _).1.rep 3 ≠ 0
  rw [← hc]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, ofHyp_3, ofHyp_4, ofHyp_5]
  refine ⟨by simp, by simp, ?_⟩
  simp [c.ne_zero]

theorem exists_normal_of_mem_fiberY {p : IsoPt} (hp : p ∈ fiberY W0 A0) :
    ∃ (a : Fin 3 → F4) (ha : bar (a 2) = a 2), p = ptA a ha := by
  obtain ⟨h4, h5, h3⟩ := mem_fiberY_W0_A0.1 hp
  set r := p.1.rep with hr
  set v : V := (r 3)⁻¹ • r with hv
  have hb : hypB v = e3 2 := by
    funext j
    fin_cases j
    · change (r 3)⁻¹ * r 5 = 0
      rw [h5, mul_zero]
    · change (r 3)⁻¹ * r 4 = 0
      rw [h4, mul_zero]
    · change (r 3)⁻¹ * r 3 = 1
      exact inv_mul_cancel₀ h3
  have hvv : v = ofHyp (hypA v) (e3 2) := by
    conv_lhs => rw [← ofHyp_hyp v, hb]
  have hiso : herm v v = 0 := by
    rw [hv, herm_smul_left, herm_smul_right, isIsoPt_of p, mul_zero, mul_zero]
  have ha : bar (hypA v 2) = hypA v 2 := by
    apply bar_eq_of_add_eq_zero
    rw [← herm_ofHyp_e3, ← hvv, hiso]
  refine ⟨hypA v, ha, ?_⟩
  conv_lhs => rw [← pt_rep p]
  refine (pt_eq_pt_iff _ _ _ _).2 ⟨r 3, ?_⟩
  rw [← hvv, hv, smul_smul, mul_inv_cancel₀ h3, one_smul]

theorem unipSU_smul_ptA (C : Matrix (Fin 3) (Fin 3) F4) (hC : IsHerm C) (a : Fin 3 → F4)
    (ha : bar (a 2) = a 2) (a' : Fin 3 → F4) (ha' : bar (a' 2) = a' 2)
    (h : a + C *ᵥ e3 2 = a') : unipSU C hC • ptA a ha = ptA a' ha' := by
  rw [ptA, ptA, smul_pt]
  congr 1
  rw [smul_def, coe_unipSU, unipMat_mulVec_ofHyp, h]

theorem hermOf_mulVec_e3 (d o : Fin 3 → F4) : hermOf d o *ᵥ e3 2 = ![o 1, o 2, d 2] := by
  funext i
  rw [mulVec_single_one]
  fin_cases i <;> rfl

theorem bar_sub_F4 : ∀ x y : F4, bar x = x → bar y = y → bar (y - x) = y - x := by decide

theorem exists_kerL_W0_ptA (a : Fin 3 → F4) (ha : bar (a 2) = a 2) (a' : Fin 3 → F4)
    (ha' : bar (a' 2) = a' 2) : ∃ x ∈ kerL W0, projAct x (ptA a ha) = ptA a' ha' := by
  set C := hermOf ![0, 0, a' 2 - a 2] ![0, a' 0 - a 0, a' 1 - a 1] with hCdef
  have hd : ∀ i, bar ((![0, 0, a' 2 - a 2] : Fin 3 → F4) i) = (![0, 0, a' 2 - a 2] : Fin 3 → F4) i
  · intro i
    fin_cases i
    · exact bar_zero
    · exact bar_zero
    · exact bar_sub_F4 _ _ ha ha'
  have hC : IsHerm C := isHerm_hermOf hd _
  refine ⟨_, mk_unipSU_mem_kerL_W0 C hC, ?_⟩
  rw [projAct_mk]
  refine unipSU_smul_ptA C hC a ha a' ha' ?_
  rw [hCdef, hermOf_mulVec_e3]
  funext i
  fin_cases i <;> simp

theorem exists_kerL_W0_of_mem_fiberY {p q : IsoPt} (hp : p ∈ fiberY W0 A0)
    (hq : q ∈ fiberY W0 A0) : ∃ x ∈ kerL W0, projAct x p = q := by
  obtain ⟨a, ha, rfl⟩ := exists_normal_of_mem_fiberY hp
  obtain ⟨a', ha', rfl⟩ := exists_normal_of_mem_fiberY hq
  exact exists_kerL_W0_ptA a ha a' ha'

theorem listOf_A0 : ∀ d o : Fin 3 → F4, (d 2 = 0 ∧ o 1 = 0 ∧ o 2 = 0) →
    ∀ w ∈ listOf d o, w 2 = 0 := by
  decide +kernel

theorem lift3_mem_A0 {w : Fin 3 → F4} (hw : w 2 = 0) : lift3 w ∈ A0 :=
  mem_A0_iff.2 ⟨hw, rfl, rfl, rfl⟩

theorem kerL_W0_inf_fixL {p : IsoPt} (hp : p ∈ fiberY W0 A0) :
    kerL W0 ⊓ fixL p = Subgroup.closure (tPt '' planePts A0) := by
  refine le_antisymm ?_ (closure_le_kerL_inf_fixL isTotIso_W0 A0_le_W0 hp)
  intro x hxx
  obtain ⟨hx, hxp⟩ := Subgroup.mem_inf.1 hxx
  obtain ⟨C, hC, rfl⟩ := (mem_kerL_W0_iff x).1 hx
  obtain ⟨a, ha, rfl⟩ := exists_normal_of_mem_fiberY hp
  rw [mem_fixL, projAct_mk, ptA, smul_pt, pt_eq_pt_iff] at hxp
  obtain ⟨c, hc⟩ := hxp
  rw [smul_def, coe_unipSU, unipMat_mulVec_ofHyp, ofHyp_smul, ofHyp_inj] at hc
  have hc1 : c = 1 := by
    have := congrFun hc.2 2
    simpa using this
  rw [hc1, one_smul] at hc
  have hCe : C *ᵥ e3 2 = 0 := by
    have h : a + C *ᵥ e3 2 = a + 0 := by rw [add_zero]; exact hc.1.symm
    exact add_left_cancel h
  have h02 : C 0 2 = 0 := by simpa [mulVec_single_one] using congrFun hCe 0
  have h12 : C 1 2 = 0 := by simpa [mulVec_single_one] using congrFun hCe 1
  have h22 : C 2 2 = 0 := by simpa [mulVec_single_one] using congrFun hCe 2
  have hd : ∀ i, bar ((fun i => C i i) i) = (fun i => C i i) i := fun i => isHerm_iff.1 hC i i
  obtain ⟨hl, hsum⟩ := listOf_spec (fun i => C i i) ![C 0 1, C 0 2, C 1 2] hd
  rw [hermOf_diag_off hC] at hsum
  have hA : ∀ w ∈ listOf (fun i => C i i) ![C 0 1, C 0 2, C 1 2], lift3 w ∈ A0 := fun w hw =>
    lift3_mem_A0 (listOf_A0 (fun i => C i i) ![C 0 1, C 0 2, C 1 2] ⟨h22, h02, h12⟩ w hw)
  have e : unipSU C hC = unipSU _ (isHerm_listSum (listOf (fun i => C i i)
      ![C 0 1, C 0 2, C 1 2])) := by
    congr 1
  rw [e]
  exact mk_unipSU_listSum_mem A0 _ hl hA _

end CFSG.Monster.B.TwoA.Unitary.Clique
