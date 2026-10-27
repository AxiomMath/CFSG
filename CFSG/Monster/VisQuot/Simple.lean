module

public import CFSG.Monster.VisQuot.NormalGen
public import CFSG.Monster.VisCert.FramePrim
public import CFSG.GroupActions.Iwasawa

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisCert

instance faithfulSMul_deltaSub : FaithfulSMul Hvis deltaSub where
  eq_of_smul_eq_smul {g₁ g₂} h := by
    have hfix : ∀ x ∈ frameDelta, ((g₂ : GLV)⁻¹ * g₁) • x = x := by
      intro x hx
      have h1 := congrArg Subtype.val (h ⟨x, hx⟩)
      rw [coe_smul_deltaSub, coe_smul_deltaSub] at h1
      rw [mul_smul]
      change (g₂ : GLV)⁻¹ • (g₁ : GLV) • x = x
      rw [h1, inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.1 (eq_one_of_forall_frameDelta hfix)).symm

instance isPreprimitive_deltaSub :
    MulAction.IsPreprimitive Hvis deltaSub :=
  (visible_frame_primitivity Hvis_stab_iff).1

theorem stabilizer_fDelta :
    MulAction.stabilizer Hvis fDelta = Nvis.subgroupOf Hvis := by
  ext h
  rw [mem_stabilizer_fDelta, Subgroup.mem_subgroupOf]
  exact Hvis_stab_iff _ h.2

instance nontrivial_Hvis : Nontrivial Hvis :=
  ⟨⟨⟨tAmb 0, tAmb_mem_Hvis 0⟩, 1, fun h => frameRep_one_ne ((tAmb_smul 0).symm.trans (by
    have h1 := congrArg (fun u : Hvis => (u : GLV) • twoΩCls) h
    simpa using h1))⟩⟩

theorem natCard_deltaSub : Nat.card deltaSub = 8292375 := by
  rw [← ncard_frameDelta, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem isSimpleGroup_Hvis :
    IsSimpleGroup Hvis :=
  CFSG.GroupActions.isSimpleGroup_of_iwasawa commutator_Hvis_eq_top fDelta (A := EH)
    (fun h hh a ha => by
      rw [stabilizer_fDelta, Subgroup.mem_subgroupOf] at hh
      have ha' : (a : GLV) ∈ Evis := ha
      exact normal_Evis_subgroupOf_Nvis.conj_mem ⟨a, Evis_le_Nvis ha'⟩ ha' ⟨h, hh⟩)
    (fun _ ha _ hb => Subtype.ext (Evis_comm ha hb)) JH_eq_top

theorem natCard_Hvis :
    Nat.card Hvis = 4157776806543360000 := by
  have h1 := (MulAction.stabilizer Hvis fDelta).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive, stabilizer_fDelta,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Nvis_le_Hvis).toEquiv, natCard_Nvis,
    natCard_deltaSub] at h1
  rw [← h1]
  norm_num

instance finite_Hvis : Finite Hvis :=
  Nat.finite_of_card_ne_zero (by rw [natCard_Hvis]; norm_num)

@[expose] def opQHom : OLqᵐᵒᵖ →* GLV where
  toFun x := (actQ x.unop).unop
  map_one' := by rw [MulOpposite.unop_one, map_one, MulOpposite.unop_one]
  map_mul' x y := by rw [MulOpposite.unop_mul, map_mul, MulOpposite.unop_mul]

theorem opQHom_op_mk (g : latticeO) :
    opQHom (MulOpposite.op (QuotientGroup.mk g)) = modTwoUnit g := rfl

theorem opQHom_injective : Function.Injective opQHom := fun x y h => by
  apply MulOpposite.unop_injective
  apply actQ_injective
  exact MulOpposite.unop_injective h

theorem range_opQHom :
    opQHom.range = Hvis := by
  ext u
  rw [MonoidHom.mem_range, Hvis_eq_OLvis, mem_OLvis]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.unop
    refine ⟨g, ?_⟩
    show modTwoUnit g = (actQ x.unop).unop
    rw [← hg]
    rfl
  · rintro ⟨g, rfl⟩
    exact ⟨MulOpposite.op (QuotientGroup.mk g), rfl⟩

def OLqOpEquivHvis : OLqᵐᵒᵖ ≃* Hvis :=
  (MonoidHom.ofInjective opQHom_injective).trans (MulEquiv.subgroupCongr range_opQHom)

theorem range_piVis :
    piVis.range = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x.unop ∈ piVis.range.unop := range_piVis_unop ▸ Subgroup.mem_top _
  exact hx

def visQuotEquiv :
    Gvis ⧸ rhoQ.subgroupOf Gvis ≃* OLqᵐᵒᵖ :=
  quotEquivRange.trans ((MulEquiv.subgroupCongr range_piVis).trans Subgroup.topEquiv)

theorem visQuotEquiv_mk
    (f : Gvis) : visQuotEquiv (QuotientGroup.mk f) = piVis f :=
  quotEquivRange_mk f

def visQuotOpEquiv :
    (Gvis)ᵐᵒᵖ ⧸ (rhoQ.subgroupOf Gvis).op ≃* OLq :=
  quotEquivRangeOp.trans
    ((MulEquiv.subgroupCongr (range_piOp.trans range_piVis_unop)).trans Subgroup.topEquiv)

theorem visQuotOpEquiv_mk (p : Pvis) :
    visQuotOpEquiv (QuotientGroup.mk (thetaGvis p)) = QuotientGroup.mk p.1.2 :=
  quotEquivRangeOp_mk p

def visQuotEquivHvis :
    Gvis ⧸ rhoQ.subgroupOf Gvis ≃* Hvis :=
  visQuotEquiv.trans OLqOpEquivHvis

def OLqEquivHvis :
    OLq ≃* Hvis := (MulEquiv.inv' OLq).trans OLqOpEquivHvis

theorem isSimpleGroup_OLq :
    IsSimpleGroup OLq :=
  haveI := isSimpleGroup_Hvis
  OLqEquivHvis.isSimpleGroup

theorem natCard_OLq :
    Nat.card OLq = 4157776806543360000 :=
  (Nat.card_congr OLqEquivHvis.toEquiv).trans natCard_Hvis

theorem isSimpleGroup_visQuot :
    IsSimpleGroup (Gvis ⧸ rhoQ.subgroupOf Gvis) :=
  haveI := isSimpleGroup_Hvis
  visQuotEquivHvis.isSimpleGroup

theorem natCard_visQuot :
    Nat.card (Gvis ⧸ rhoQ.subgroupOf Gvis) = 4157776806543360000 :=
  (Nat.card_congr visQuotEquivHvis.toEquiv).trans natCard_Hvis

theorem isSimpleGroup_visQuotOp :
    IsSimpleGroup ((Gvis)ᵐᵒᵖ ⧸ (rhoQ.subgroupOf Gvis).op) :=
  haveI := isSimpleGroup_OLq
  visQuotOpEquiv.isSimpleGroup

theorem natCard_visQuotOp :
    Nat.card ((Gvis)ᵐᵒᵖ ⧸ (rhoQ.subgroupOf Gvis).op) = 4157776806543360000 :=
  (Nat.card_congr visQuotOpEquiv.toEquiv).trans natCard_OLq

theorem visible_quotient_simple :
    IsSimpleGroup (Gvis ⧸ rhoQ.subgroupOf Gvis) ∧ Nontrivial (Gvis ⧸ rhoQ.subgroupOf Gvis) ∧
    Finite (Gvis ⧸ rhoQ.subgroupOf Gvis) ∧
    Nat.card (Gvis ⧸ rhoQ.subgroupOf Gvis) = 4157776806543360000 ∧
    piVis.range = ⊤ ∧ (∀ f : Gvis, visQuotEquiv (QuotientGroup.mk f) = piVis f) ∧
    Function.Injective actQ ∧ IsSimpleGroup OLq ∧ Nat.card OLq = 4157776806543360000 ∧
    IsSimpleGroup ((Gvis)ᵐᵒᵖ ⧸ (rhoQ.subgroupOf Gvis).op) ∧
    Nat.card ((Gvis)ᵐᵒᵖ ⧸ (rhoQ.subgroupOf Gvis).op) = 4157776806543360000 ∧
    (∀ p : Pvis, visQuotOpEquiv (QuotientGroup.mk (thetaGvis p)) = QuotientGroup.mk p.1.2) ∧
    IsSimpleGroup Hvis ∧ Nat.card Hvis = 4157776806543360000 ∧
    Nat.card deltaSub = 8292375 ∧ Nat.card Nvis = 2 ^ 11 * 244823040 :=
  ⟨isSimpleGroup_visQuot, isSimpleGroup_visQuot.toNontrivial,
    Nat.finite_of_card_ne_zero (by rw [natCard_visQuot]; norm_num), natCard_visQuot, range_piVis,
    visQuotEquiv_mk, actQ_injective, isSimpleGroup_OLq, natCard_OLq, isSimpleGroup_visQuotOp,
    natCard_visQuotOp, visQuotOpEquiv_mk, isSimpleGroup_Hvis, natCard_Hvis, natCard_deltaSub,
    natCard_Nvis⟩

end CFSG.Monster.VisQuot
