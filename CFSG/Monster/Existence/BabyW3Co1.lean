module

public import CFSG.Sporadic.Co1.Module.OddCent
public import CFSG.Monster.Existence.Co1Bridge
import all CFSG.Monster.Existence.Co1Bridge
public import CFSG.Monster.Existence.ELevelCheck
import all CFSG.Monster.VisQuot.Simple
public import CFSG.Monster.Existence.BabyW3Count
public import CFSG.Monster.Existence.BabyW3Fix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Visible CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Existence.Co1Bridge CFSG.Blueprint Matrix

@[expose] noncomputable def e1Co1 :
    NativeSporadic.Co1 ≃* (Submonoid.closure
    ({(gA24 : Matrix (Fin 24) (Fin 24) (ZMod 2)), (gB24 : Matrix (Fin 24) (Fin 24) (ZMod 2))} :
      Set (Matrix (Fin 24) (Fin 24) (ZMod 2))))ˣ :=
  Units.mapEquiv (MulEquiv.submonoidCongr seedMonoid_eq)

private theorem co1EquivJ24_eq :
    co1EquivJ24 = e1Co1.trans (NativeSporadic.unitSeedEquiv gA24 gB24) := rfl

theorem val_e1Co1 (r : NativeSporadic.Co1) :
    ((e1Co1 r : (Submonoid.closure
      ({(gA24 : Matrix (Fin 24) (Fin 24) (ZMod 2)), (gB24 : Matrix (Fin 24) (Fin 24) (ZMod 2))} :
        Set (Matrix (Fin 24) (Fin 24) (ZMod 2))))ˣ) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      (r : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
  val_mapEquiv_submonoidCongr seedMonoid_eq r

theorem co1EquivJ24_val (r : NativeSporadic.Co1) :
    ((co1EquivJ24 r : J24) : GL (Fin 24) (ZMod 2)).val =
      (r : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  rw [co1EquivJ24_eq, MulEquiv.trans_apply]
  exact (NativeSporadic.unitSeedEquiv_val gA24 gB24 (e1Co1 r)).trans (val_e1Co1 r)

@[expose] noncomputable def uHvis :
    Hvis := ⟨monoN 1, modTwoUnit_mem_Hvis' (monoAO 1)⟩

theorem uHvis_mul_self :
    uHvis * uHvis = 1 := by
  obtain ⟨-, -, hmem, -⟩ := lattice_quotient_three_involution_classes
  exact Subtype.ext (hmem 1 (by simp)).2.1

theorem uHvis_ne_one :
    uHvis ≠ 1 := by
  obtain ⟨-, -, hmem, -⟩ := lattice_quotient_three_involution_classes
  exact fun h => (hmem 1 (by simp)).2.2 (congrArg Subtype.val h)

theorem orderOf_uHvis :
    orderOf uHvis = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact uHvis_mul_self) uHvis_ne_one

@[expose] noncomputable def rCo1 :
    NativeSporadic.Co1 := co1EquivHvis.symm uHvis

theorem orderOf_rCo1 :
    orderOf rCo1 = 2 := by
  rw [rCo1, MulEquiv.orderOf_eq]
  exact orderOf_uHvis

@[expose] def fixKappa1 : Set L2 :=
  {v | ((monoN 1 : GLV) : Module.End (ZMod 2) L2) v = v}

theorem ncard_fixKappa1 :
    fixKappa1.ncard = 2 ^ 16 := by
  have hset : fixKappa1 =
      vecX '' ↑((Finset.range (2 ^ 24)).filter fun x => kapX (tT 1) (tD 1) x = x) := by
    ext v
    constructor
    · intro hv
      refine ⟨packOf v, ?_, vecX_packOf v⟩
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨packOf_lt v, ?_⟩
      apply vecX_injective_lt (kapX_lt _ _ _) (packOf_lt v)
      rw [← modTwoEnd_vecX, vecX_packOf]
      exact hv
    · rintro ⟨x, hx, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
      show modTwoEnd (cosetPair 1).1.2 (vecX x) = vecX x
      rw [modTwoEnd_vecX, hx.2]
  rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, fix_count_kap_one]
  intro x hx y hy h
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy
  exact vecX_injective_lt hx.1 hy.1 h

theorem ncard_co1Fix_eq
    (r : NativeSporadic.Co1) :
    (CFSG.Monster.GMS.co1Fix r).ncard =
      {v : L2 | (((co1EquivHvis r : Hvis) : GLV) : Module.End (ZMod 2) L2) v = v}.ncard := by
  set g : GL (Fin 24) (ZMod 2) := ((co1EquivJ24 r : J24) : GL (Fin 24) (ZMod 2)) with hg
  have hmat : (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      (r : Matrix (Fin 24) (Fin 24) (ZMod 2)) := co1EquivJ24_val r
  have hco : ((co1EquivHvis r : Hvis) : GLV) = conjHom g := rfl
  have key : {v : L2 | (((co1EquivHvis r : Hvis) : GLV) : Module.End (ZMod 2) L2) v = v} =
      Co1Bridge.theta '' CFSG.Monster.GMS.co1Fix r := by
    ext v
    constructor
    · intro hv
      refine ⟨Co1Bridge.theta.symm v, ?_, Co1Bridge.theta.apply_symm_apply v⟩
      rw [hco] at hv
      have hv' : ((conjHom g : GLV) : L2 →ₗ[ZMod 2] L2) v = v := hv
      rw [conjHom_apply] at hv'
      have h1 : g *ᵥ Co1Bridge.theta.symm v = Co1Bridge.theta.symm v := by
        apply Co1Bridge.theta.injective
        rw [Co1Bridge.theta.apply_symm_apply]
        exact hv'
      show (r : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ Co1Bridge.theta.symm v =
        Co1Bridge.theta.symm v
      rw [← hmat]
      exact h1
    · rintro ⟨w, hw, rfl⟩
      rw [hco]
      show ((conjHom g : GLV) : L2 →ₗ[ZMod 2] L2) (Co1Bridge.theta w) = Co1Bridge.theta w
      rw [conjHom_apply, Co1Bridge.theta.symm_apply_apply]
      have hw' : (r : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w := hw
      rw [← hmat] at hw'
      rw [hw']
  rw [key, Set.ncard_image_of_injective _ Co1Bridge.theta.injective]

theorem ncard_fix_rCo1 :
    (CFSG.Monster.GMS.co1Fix rCo1).ncard = 2 ^ 16 := by
  rw [ncard_co1Fix_eq, rCo1, MulEquiv.apply_symm_apply]
  exact ncard_fixKappa1

theorem natCard_centralizer_of_fix
    {r : NativeSporadic.Co1} (hr : orderOf r = 2)
    (hf : (CFSG.Monster.GMS.co1Fix r).ncard = 2 ^ 16) :
    Nat.card ↥(Subgroup.centralizer ({r} : Set NativeSporadic.Co1)) =
      2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7 := by
  obtain ⟨-, -, hmem, hcls, -⟩ := lattice_quotient_three_involution_classes
  obtain ⟨c, hc⟩ := CFSG.Sporadic.Co1.Module.exists_conj_three_of_chevalley monoN hmem hcls
  obtain ⟨sA, sB, sC, hrep⟩ := CFSG.Sporadic.Co1.Module.rep_facts
  have hcl := CFSG.Monster.GMS.co1Inv_classes hrep c hc
  obtain ⟨hoA, hoB, hoC, hfA, hfB, hfC, -⟩ := hrep
  have hA : ∀ s : NativeSporadic.Co1, orderOf s = 2 → (CFSG.Monster.GMS.co1Fix s).ncard = 2 ^ 16 →
      IsConj s sA := by
    intro s hs hfs
    rcases hcl s hs with h | h | h
    · exact h
    · have := (CFSG.Monster.GMS.co1Inv_isConj_invariants h).1
      rw [hfs] at this
      have e : (CFSG.Monster.GMS.co1Fix sB).ncard = 2 ^ 12 := hfB
      rw [e] at this
      norm_num at this
    · have := (CFSG.Monster.GMS.co1Inv_isConj_invariants h).1
      rw [hfs] at this
      have e : (CFSG.Monster.GMS.co1Fix sC).ncard = 2 ^ 12 := hfC
      rw [e] at this
      norm_num at this
  have h1 := hA r hr hf
  have h2 := hA _ CFSG.Sporadic.Co1.Module.Odd.orderOf_rho3
    CFSG.Sporadic.Co1.Module.Odd.rho3_ncard_fix
  have h3 := (CFSG.Monster.GMS.co1Inv_isConj_invariants (h1.trans h2.symm)).2.2
  rw [h3]
  have h4 := CFSG.Sporadic.Co1.Module.Odd.isCo1TwoA_rho3.2
  rw [CFSG.Sporadic.Co1.Module.Odd.rho3_ncard_fix] at h4
  omega

theorem OLqOpEquivHvis_piVis_cosetRep_one :
    OLqOpEquivHvis (piVis (cosetRep 1)) = uHvis := by
  rw [piVis_cosetRep]
  apply Subtype.ext
  show opQHom (MulOpposite.op (QuotientGroup.mk (monoAO 1))) = monoN 1
  exact opQHom_op_mk (monoAO 1)

theorem natCard_centralizer_piVis_cosetRep_one :
    Nat.card ↥(Subgroup.centralizer ({piVis (cosetRep 1)} :
      Set (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ)) = 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have h1 := natCard_centralizer_eq_image OLqOpEquivHvis (piVis (cosetRep 1))
  rw [OLqOpEquivHvis_piVis_cosetRep_one] at h1
  have h2 := @natCard_centralizer_eq_image Hvis NativeSporadic.Co1 _ Units.instGroup
    co1EquivHvis.symm uHvis
  rw [h1, h2]
  exact natCard_centralizer_of_fix orderOf_rCo1 ncard_fix_rCo1

end CFSG.Monster.Existence
