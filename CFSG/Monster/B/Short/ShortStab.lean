module

public import CFSG.Monster.B.Short.LatticeForm
public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.VisCert.Delta

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Visible Module
  Matrix

private theorem zmod_two_cases'' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

abbrev bL : LinearMap.BilinForm (ZMod 2) L2 := QuadraticMap.polarBilin qL

theorem bL_apply (x y : L2) : bL x y = QuadraticMap.polar qL x y := rfl

theorem bL_comm (x y : L2) : bL x y = bL y x := QuadraticMap.polar_comm _ x y

theorem bL_self (x : L2) : bL x x = 0 := by
  rw [bL_apply, QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]

theorem qL_add (x y : L2) : qL (x + y) = qL x + qL y + bL x y := by
  rw [bL_apply, QuadraticMap.polar]
  ring

theorem bL_mk (x y : LL) :
    bL (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = ((hInt (x : Fin 24 → ℤ) y : ℤ) : ZMod 2) :=
  polarBilin_codeQuadForm_mk allOnes_mem_C weight_mod_four' x y

@[expose] def Kstab (v : L2) : Subgroup OLq := (MulAction.stabilizer GLV v).op.comap actQ

theorem mk_mem_Kstab_iff (v : L2) (g : latticeO) :
    (QuotientGroup.mk g : OLq) ∈ Kstab v ↔ modTwoEnd g v = v := Iff.rfl

@[expose] def vPerpL (v : L2) : Submodule (ZMod 2) L2 := LinearMap.ker (bL v)

@[expose] def vLineL (v : L2) : Submodule (ZMod 2) L2 := Submodule.span (ZMod 2) {v}

theorem vLineL_le_vPerpL (v : L2) : vLineL v ≤ vPerpL v := by
  rw [vLineL, Submodule.span_le, Set.singleton_subset_iff]
  exact bL_self v

@[expose] def vLineInL (v : L2) : Submodule (ZMod 2) (vPerpL v) :=
  (vLineL v).comap (vPerpL v).subtype

abbrev Wv (v : L2) : Type := vPerpL v ⧸ vLineInL v

theorem mem_vLineL {v x : L2} : x ∈ vLineL v ↔ x = 0 ∨ x = v := by
  rw [vLineL, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases zmod_two_cases'' a with rfl | rfl
    · exact .inl (zero_smul _ _)
    · exact .inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

@[expose] def qWFun (v : L2) (hv : qL v = 0) : Wv v → ZMod 2 :=
  Quotient.lift (s := (vLineInL v).quotientRel) (fun x => qL (x : L2)) (by
    intro x y hxy
    have h0 : x - y ∈ vLineInL v := (Submodule.quotientRel_def (vLineInL v)).1 hxy
    have h : ((x : L2) - y) ∈ vLineL v := h0
    rcases mem_vLineL.1 h with h | h
    · rw [sub_eq_zero.1 h]
    · have hx : (x : L2) = y + v := by rw [add_comm]; exact sub_eq_iff_eq_add.1 h
      change qL (x : L2) = qL (y : L2)
      rw [hx, qL_add, hv, add_zero, bL_comm]
      have : bL v y = 0 := y.2
      rw [this, add_zero])

theorem qWFun_mk (v : L2) (hv : qL v = 0) (x : vPerpL v) :
    qWFun v hv (Submodule.Quotient.mk x) = qL (x : L2) := rfl

theorem polar_qWFun_mk (v : L2) (hv : qL v = 0) (x y : vPerpL v) :
    QuadraticMap.polar (qWFun v hv) (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      bL x y := by
  rw [QuadraticMap.polar, ← Submodule.Quotient.mk_add, qWFun_mk, qWFun_mk, qWFun_mk]
  rfl

@[expose] def qW (v : L2) (hv : qL v = 0) : QuadraticForm (ZMod 2) (Wv v) :=
  QuadraticMap.ofPolar (qWFun v hv)
    (by
      intro a x
      induction x using Submodule.Quotient.induction_on with | H x => ?_
      rcases zmod_two_cases'' a with rfl | rfl
      · rw [zero_smul, ← Submodule.Quotient.mk_zero, qWFun_mk, zero_mul, zero_smul]
        exact QuadraticMap.map_zero qL
      · rw [one_smul, mul_one, one_smul])
    (by
      intro x x' y
      induction x using Submodule.Quotient.induction_on with | H x => ?_
      induction x' using Submodule.Quotient.induction_on with | H x' => ?_
      induction y using Submodule.Quotient.induction_on with | H y => ?_
      rw [← Submodule.Quotient.mk_add, polar_qWFun_mk, polar_qWFun_mk, polar_qWFun_mk,
        Submodule.coe_add, map_add, LinearMap.add_apply])
    (by
      intro a x y
      induction x using Submodule.Quotient.induction_on with | H x => ?_
      induction y using Submodule.Quotient.induction_on with | H y => ?_
      rw [← Submodule.Quotient.mk_smul, polar_qWFun_mk, polar_qWFun_mk, Submodule.coe_smul,
        map_smul, LinearMap.smul_apply])

theorem qW_mk (v : L2) (hv : qL v = 0) (x : vPerpL v) :
    qW v hv (Submodule.Quotient.mk x) = qL (x : L2) := rfl

theorem polarBilin_qW_mk (v : L2) (hv : qL v = 0) (x y : vPerpL v) :
    QuadraticMap.polarBilin (qW v hv) (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      bL x y :=
  polar_qWFun_mk v hv x y

theorem exists_bL_eq_one {v : L2} (hv : v ≠ 0) : ∃ y, bL v y = 1 := by
  by_contra h
  push Not at h
  apply hv
  refine bL_nondegenerate.1 v fun y => ?_
  rcases zmod_two_cases'' (bL v y) with h0 | h1
  · exact h0
  · exact absurd h1 (h y)

theorem finrank_vPerpL {v : L2} (hv : v ≠ 0) : finrank (ZMod 2) (vPerpL v) = 23 := by
  obtain ⟨y, hy⟩ := exists_bL_eq_one hv
  have hrange : LinearMap.range (bL v) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • y, by rw [map_smul, hy, smul_eq_mul, mul_one]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (bL v)
  rw [hrange, finrank_top, Module.finrank_self, finrank_L2] at h
  change finrank (ZMod 2) (LinearMap.ker (bL v)) = 23
  omega

theorem finrank_vLineInL {v : L2} (hv : v ≠ 0) : finrank (ZMod 2) (vLineInL v) = 1 :=
  (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (vLineL_le_vPerpL v))).trans
    (finrank_span_singleton hv)

theorem finrank_Wv {v : L2} (hv : v ≠ 0) : finrank (ZMod 2) (Wv v) = 22 := by
  have h := Submodule.finrank_quotient_add_finrank (vLineInL v)
  rw [finrank_vLineInL hv, finrank_vPerpL hv] at h
  change finrank (ZMod 2) (vPerpL v ⧸ vLineInL v) = 22
  omega

theorem orthogonal_vPerpL {v : L2} (hv : v ≠ 0) : bL.orthogonal (vPerpL v) = vLineL v := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [vLineL, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [bL_comm]
    exact hn
  · rw [LinearMap.BilinForm.finrank_orthogonal bL_nondegenerate, finrank_L2, finrank_vPerpL hv,
      vLineL, finrank_span_singleton hv]

theorem polarBilin_qW_nondegenerate {v : L2} (hv0 : v ≠ 0) (hv : qL v = 0) :
    (QuadraticMap.polarBilin (qW v hv)).Nondegenerate := by
  have key : ∀ x : vPerpL v, (∀ y : vPerpL v, bL x y = 0) →
      (Submodule.Quotient.mk x : Wv v) = 0 := by
    intro x hx
    rw [Submodule.Quotient.mk_eq_zero]
    change (x : L2) ∈ vLineL v
    rw [← orthogonal_vPerpL hv0, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [bL_comm]
    exact hx ⟨n, hn⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine key x fun y => ?_
      have := hx (Submodule.Quotient.mk y)
      rwa [polarBilin_qW_mk] at this
  · induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine key x fun y => ?_
      have := hx (Submodule.Quotient.mk y)
      rwa [polarBilin_qW_mk, bL_comm] at this

@[expose] def kOp (k : OLq) : Module.End (ZMod 2) L2 := ((actQ k).unop : GLV)

theorem kOp_mk (g : latticeO) : kOp (QuotientGroup.mk g) = modTwoEnd g := rfl

theorem kOp_one : kOp 1 = 1 := by
  rw [kOp, map_one, MulOpposite.unop_one, Units.val_one]

theorem kOp_mul (k k' : OLq) : kOp (k * k') = kOp k' * kOp k := by
  rw [kOp, kOp, kOp, map_mul, MulOpposite.unop_mul, Units.val_mul]

theorem bL_modTwoEnd (g : latticeO) (x y : L2) : bL (modTwoEnd g x) (modTwoEnd g y) = bL x y := by
  rw [bL_apply, bL_apply, QuadraticMap.polar, QuadraticMap.polar, ← map_add, qL_modTwoEnd,
    qL_modTwoEnd, qL_modTwoEnd]

theorem bL_kOp (k : OLq) (x y : L2) : bL (kOp k x) (kOp k y) = bL x y := by
  induction k using QuotientGroup.induction_on with
  | H g => exact bL_modTwoEnd g x y

theorem kOp_of_mem_Kstab {v : L2} {k : OLq} (hk : k ∈ Kstab v) : kOp k v = v := hk

theorem kOp_mem_vPerpL {v : L2} {k : OLq} (hk : k ∈ Kstab v) {x : L2} (hx : x ∈ vPerpL v) :
    kOp k x ∈ vPerpL v := by
  change bL v (kOp k x) = 0
  rw [← kOp_of_mem_Kstab hk, bL_kOp]
  exact hx

theorem kOp_mem_vLineL {v : L2} {k : OLq} (hk : k ∈ Kstab v) {x : L2} (hx : x ∈ vLineL v) :
    kOp k x ∈ vLineL v := by
  rcases mem_vLineL.1 hx with rfl | rfl
  · rw [map_zero]
    exact zero_mem _
  · rw [kOp_of_mem_Kstab hk]
    exact Submodule.mem_span_singleton_self _

@[expose] def wAct (v : L2) (k : Kstab v) : Module.End (ZMod 2) (Wv v) :=
  Submodule.mapQ (vLineInL v) (vLineInL v)
    ((kOp k).restrict fun _ hx => kOp_mem_vPerpL k.2 hx) (fun _ hx => kOp_mem_vLineL k.2 hx)

theorem wAct_mk (v : L2) (k : Kstab v) (x : vPerpL v) :
    wAct v k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨kOp k x, kOp_mem_vPerpL k.2 x.2⟩ := rfl

@[expose] def KvAct (v : L2) : Kstab v →* (Module.End (ZMod 2) (Wv v))ᵐᵒᵖ where
  toFun k := MulOpposite.op (wAct v k)
  map_one' := by
    rw [← MulOpposite.op_one]
    congr 1
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [wAct_mk, Module.End.one_apply]
      congr 1
      exact Subtype.ext (LinearMap.congr_fun kOp_one (x : L2))
  map_mul' k k' := by
    rw [← MulOpposite.op_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Module.End.mul_apply, wAct_mk, wAct_mk, wAct_mk]
      congr 1
      exact Subtype.ext (LinearMap.congr_fun (kOp_mul k k') (x : L2))

theorem wAct_eq_of_KvAct {v : L2} {k : Kstab v} (h : KvAct v k = 1) : wAct v k = 1 :=
  MulOpposite.op_injective h

theorem latHom_negOneO (x : LL) : latHom negOneO x = -x := by
  apply Subtype.ext
  apply ratVec_injective
  rw [ratVec_latHom, mat_negOneO, vecMul_neg, vecMul_one]
  exact (ScalarKernel.ratVec_neg _).symm

theorem latHom_eq_of_ratVec {g : latticeO} {u : LL}
    (h : ScalarKernel.ratVec (u : Fin 24 → ℤ) ᵥ* mat g = ScalarKernel.ratVec u) :
    latHom g u = u :=
  Subtype.ext (ratVec_injective ((ratVec_latHom g u).trans h))

theorem ratVec_of_latHom_eq {g : latticeO} {u : LL} (h : latHom g u = u) :
    ScalarKernel.ratVec (u : Fin 24 → ℤ) ᵥ* mat g = ScalarKernel.ratVec u :=
  (ratVec_latHom g u).symm.trans (congrArg (fun w : LL => ScalarKernel.ratVec w) h)

theorem classOf_coe (x : LL) : classOf (x : Fin 24 → ℤ) = Submodule.Quotient.mk x :=
  classOf_of_mem x.2

theorem latHom_eq_or_eq_neg {u : Fin 24 → ℤ} (hu : u ∈ minVecs) {g : latticeO}
    (hg : modTwoEnd g (classOf u) = classOf u) :
    latHom g ⟨u, hu.1⟩ = ⟨u, hu.1⟩ ∨ latHom g ⟨u, hu.1⟩ = -⟨u, hu.1⟩ := by
  have hm := latVec_mem_minVecs g hu
  have hcl : classOf u = classOf (latVec (mat g) u) := by
    rw [classOf_latVec g hu.1, hg]
  rcases (classOf_eq_iff hu hm).1 hcl with h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (Subtype.ext h)

theorem exists_rep_fix {u : Fin 24 → ℤ} (hu : u ∈ minVecs) {k : OLq}
    (hk : k ∈ Kstab (classOf u)) :
    ∃ g : latticeO, (QuotientGroup.mk g : OLq) = k ∧ latHom g ⟨u, hu.1⟩ = ⟨u, hu.1⟩ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  rcases latHom_eq_or_eq_neg hu hk with h | h
  · exact ⟨g, rfl, h⟩
  · refine ⟨g * negOneO, ?_, ?_⟩
    · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff negOneO).2 (Subgroup.mem_zpowers _),
        mul_one]
    · rw [latHom_mul, h, map_neg, latHom_negOneO, neg_neg]

@[expose] def OLstab (u : Fin 24 → ℤ) : Subgroup latticeO where
  carrier := {g | ScalarKernel.ratVec u ᵥ* mat g = ScalarKernel.ratVec u}
  one_mem' := by
    change ScalarKernel.ratVec u ᵥ* mat 1 = ScalarKernel.ratVec u
    rw [mat_one, vecMul_one]
  mul_mem' := fun {g g'} hg hg' => by
    change ScalarKernel.ratVec u ᵥ* mat (g * g') = ScalarKernel.ratVec u
    rw [mat_mul, ← vecMul_vecMul, show ScalarKernel.ratVec u ᵥ* mat g = ScalarKernel.ratVec u
      from hg, show ScalarKernel.ratVec u ᵥ* mat g' = ScalarKernel.ratVec u from hg']
  inv_mem' := fun {g} hg => by
    change ScalarKernel.ratVec u ᵥ* mat g⁻¹ = ScalarKernel.ratVec u
    have hg' : ScalarKernel.ratVec u ᵥ* mat g = ScalarKernel.ratVec u := hg
    calc ScalarKernel.ratVec u ᵥ* mat g⁻¹ = (ScalarKernel.ratVec u ᵥ* mat g) ᵥ* mat g⁻¹ := by
          rw [hg']
      _ = ScalarKernel.ratVec u := by
          rw [vecMul_vecMul, ← mat_mul, mul_inv_cancel, mat_one, vecMul_one]

theorem mem_OLstab_iff {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (g : latticeO) :
    g ∈ OLstab u ↔ latHom g ⟨u, hu⟩ = ⟨u, hu⟩ :=
  ⟨fun h => latHom_eq_of_ratVec h, fun h => ratVec_of_latHom_eq h⟩

theorem mk_mem_Kstab_of_mem_OLstab {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) {g : latticeO}
    (hg : g ∈ OLstab u) : (QuotientGroup.mk g : OLq) ∈ Kstab (classOf u) := by
  rw [mk_mem_Kstab_iff, classOf_of_mem hu, modTwoEnd_mk, (mem_OLstab_iff hu g).1 hg]

@[expose] def stabRes {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    OLstab u →* Kstab (classOf u) :=
  ((QuotientGroup.mk' (Subgroup.zpowers negOneO)).comp (OLstab u).subtype).codRestrict
    (Kstab (classOf u)) fun g => mk_mem_Kstab_of_mem_OLstab hu g.2

theorem coe_stabRes {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (g : OLstab u) :
    (stabRes hu g : OLq) = QuotientGroup.mk (g : latticeO) := rfl

theorem stabRes_injective {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : Function.Injective (stabRes hu.1) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (QuotientGroup.mk (g : latticeO) : OLq) = 1 := congrArg Subtype.val hg
  rw [QuotientGroup.eq_one_iff, mem_zpowers_negOneO_iff] at h1
  rcases h1 with h1 | h1
  · exact Subtype.ext h1
  · exfalso
    have hfix := (mem_OLstab_iff hu.1 g).1 g.2
    rw [h1, latHom_negOneO] at hfix
    have h0 : (⟨u, hu.1⟩ : LL) = 0 := by
      have h2 : (2 : ℤ) • (⟨u, hu.1⟩ : LL) = 0 := by
        rw [two_smul]
        nth_rw 1 [← hfix]
        exact neg_add_cancel _
      exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
    exact minVecs_ne_zero hu (congrArg Subtype.val h0)

theorem stabRes_surjective {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    Function.Surjective (stabRes hu.1) := by
  intro k
  obtain ⟨g, hgk, hgu⟩ := exists_rep_fix hu k.2
  exact ⟨⟨g, (mem_OLstab_iff hu.1 g).2 hgu⟩, Subtype.ext hgk⟩

@[expose] def stabResEquiv {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : OLstab u ≃* Kstab (classOf u) :=
  MulEquiv.ofBijective (stabRes hu.1) ⟨stabRes_injective hu, stabRes_surjective hu⟩

theorem stabResEquiv_apply {u : Fin 24 → ℤ} (hu : u ∈ minVecs) (g : OLstab u) :
    stabResEquiv hu g = stabRes hu.1 g := rfl

theorem htriv_of_KvAct {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (g : latticeO)
    (hk : (QuotientGroup.mk g : OLq) ∈ Kstab (classOf u))
    (h1 : KvAct (classOf u) ⟨QuotientGroup.mk g, hk⟩ = 1) (x : LL) (hx : Even (hInt u x)) :
    ∃ m : ℤ, ∃ t : LL, latHom g x = x + m • ⟨u, hu⟩ + (2 : ℤ) • t := by
  have hxv : (Submodule.Quotient.mk x : L2) ∈ vPerpL (classOf u) := by
    change bL (classOf u) (Submodule.Quotient.mk x) = 0
    rw [classOf_of_mem hu, bL_mk]
    obtain ⟨k, hk⟩ := hx
    rw [hk]
    push_cast
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have h2 := LinearMap.congr_fun (wAct_eq_of_KvAct h1) (Submodule.Quotient.mk ⟨_, hxv⟩)
  rw [wAct_mk, Module.End.one_apply, Submodule.Quotient.eq] at h2
  change kOp (QuotientGroup.mk g) (Submodule.Quotient.mk x) - Submodule.Quotient.mk x ∈
    vLineL (classOf u) at h2
  rw [kOp_mk, modTwoEnd_mk, classOf_of_mem hu] at h2
  rcases mem_vLineL.1 h2 with h3 | h3
  · rw [sub_eq_zero, modN_two_mk_eq_mk_iff] at h3
    obtain ⟨t, ht⟩ := h3
    exact ⟨0, t, by rw [zero_smul, add_zero, ← ht]; abel⟩
  · rw [sub_eq_iff_eq_add, ← Submodule.Quotient.mk_add, modN_two_mk_eq_mk_iff] at h3
    obtain ⟨t, ht⟩ := h3
    exact ⟨1, t, by rw [one_smul, ← ht]; abel⟩

theorem KvAct_injective_of_transport {u : Fin 24 → ℤ} (hu : u ∈ minVecs) (g₂ : latticeO)
    (hg₂ : latHom g₂ ⟨u, hu.1⟩ = uL) : Function.Injective (KvAct (classOf u)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨k, hk⟩ h1
  obtain ⟨g, rfl, hgu⟩ := exists_rep_fix hu hk
  have htriv := htriv_of_KvAct hu.1 g hk h1
  set g' : latticeO := g₂⁻¹ * g * g₂ with hg'
  have hinv : ∀ x : LL, latHom g₂ (latHom g₂⁻¹ x) = x := fun x => by
    rw [← latHom_mul, inv_mul_cancel, latHom_one]
  have hinv' : latHom g₂⁻¹ uL = ⟨u, hu.1⟩ := by
    rw [← hg₂, ← latHom_mul, mul_inv_cancel, latHom_one]
  have hg'u : latHom g' uL = uL := by
    rw [hg', latHom_mul, latHom_mul, hinv', hgu, hg₂]
  have htriv' : ∀ x : LL, Even (hL uL x) →
      ∃ m : ℤ, ∃ t : LL, latHom g' x = x + m • uL + (2 : ℤ) • t := by
    intro x hx
    have hy : Even (hInt u (latHom g₂⁻¹ x)) := by
      have e : hL (latHom g₂ ⟨u, hu.1⟩) (latHom g₂ (latHom g₂⁻¹ x)) =
          hL ⟨u, hu.1⟩ (latHom g₂⁻¹ x) := hL_latHom g₂ _ _
      rw [hg₂, hinv] at e
      rw [← hL_apply ⟨u, hu.1⟩, ← e]
      exact hx
    obtain ⟨m, t, hmt⟩ := htriv _ hy
    refine ⟨m, latHom g₂ t, ?_⟩
    rw [hg', latHom_mul, latHom_mul, hmt, map_add, map_add, map_zsmul, map_zsmul, hinv, hg₂]
  have h1' := eq_one_of_trivial_mod_two_uL g' hg'u htriv'
  have hg1 : g = 1 := by
    have : g₂ * g' * g₂⁻¹ = g := by rw [hg']; group
    rw [← this, h1', mul_one, mul_inv_cancel]
  apply Subtype.ext
  change (QuotientGroup.mk g : OLq) = 1
  rw [hg1, QuotientGroup.mk_one]

theorem KvAct_injective_vMinus : Function.Injective (KvAct (classOf (vMinus 0 1))) :=
  KvAct_injective_of_transport vMinus_zero_one_mem 1 (latHom_one _)

end CFSG.Monster.B.Short
