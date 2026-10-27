module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

instance instNormalSubgroupOfPc (M V : Subgroup G) : (V.subgroupOf (Pc M V)).Normal where
  conj_mem v hv p := by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    have hcen : (p : G) ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_inf.mp p.2).2
    have hcomm : (v : G) * (p : G) = (p : G) * (v : G) :=
      Subgroup.mem_centralizer_iff.mp hcen v hv
    have hconj : (p : G) * (v : G) * (p : G)⁻¹ = (v : G) := by
      rw [← hcomm]
      group
    change (p : G) * (v : G) * (p : G)⁻¹ ∈ V
    rw [hconj]
    exact hv

theorem Sec6Hyp.pbarHyp (hS : Sec6Hyp M V) : QuotMod.Hyp M (Pc M V) V where
  le := hS.sec5.toRootHyp.toHyp.le_Pc
  comm := by
    intro x hx y hy
    have h := Subgroup.commutator_mem_commutator hx hy
    rwa [hS.sec5.commutator_Pc_eq_V hS.ne] at h
  conj := by
    intro g hg x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact ((inSubgroup_pCore_two M).2.2 hg x).mp hx.1
    · exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer (hS.sec5.toRootHyp.toHyp.le_normalizer hg)) x).mp hx.2
  conj₀ := by
    intro g hg x hx
    exact (Subgroup.mem_normalizer_iff.mp
      (hS.sec5.toRootHyp.toHyp.le_normalizer hg) x).mp hx

@[reducible] noncomputable def Sec6Hyp.pbarModule (hS : Sec6Hyp M V) :
    Module (ZMod 2) (SecMod hS.pbarHyp) :=
  SecMod.module hS.pbarHyp fun x hx =>
    Hyp.mul_self_mem_of_mem_Pc hS.sec5.toRootHyp.toHyp hx

noncomputable def Sec6Hyp.pbarRep (hS : Sec6Hyp M V)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] :
    Representation (ZMod 2) (MBar M) (SecMod hS.pbarHyp) :=
  secDescend hS.pbarHyp (QuotientGroup.mk' (pCore 2 ↥M))
    (QuotientGroup.mk'_surjective _) fun z hz => by
      refine secConj_eq_one hS.pbarHyp fun x hx => ?_
      have hzP : (z : G) ∈ Pc M V := (hS.mk_eq_one_iff z).mp hz
      have hcomm : ⁅(z : G), x⁆ ∈ V := by
        have h := Subgroup.commutator_mem_commutator hzP hx
        rwa [hS.sec5.commutator_Pc_eq_V hS.ne] at h
      simpa only [commutatorElement_def] using hcomm

theorem Sec6Hyp.pbarRep_mk (hS : Sec6Hyp M V)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] (z : ↥M) (x : ↥(Pc M V)) :
    hS.pbarRep (QuotientGroup.mk' (pCore 2 ↥M) z) (SecMod.mk hS.pbarHyp x) =
      SecMod.mk hS.pbarHyp ⟨(z : G) * x * (z : G)⁻¹, hS.pbarHyp.conj z z.2 x x.2⟩ := by
  rw [Sec6Hyp.pbarRep, secDescend_apply, secConj_mk]

theorem Sec6Hyp.span_pbarRep_imgQ (hS : Sec6Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) [Module (ZMod 2) (SecMod hS.pbarHyp)] :
    Submodule.span (ZMod 2) {u | ∃ a ∈ imgQ M U, ∃ w, u = hS.pbarRep a w - w} =
      subSec hS.pbarHyp ⁅Pc M V, U⁆ := by
  have hUM : U ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hU).1
  have hset : {u | ∃ a ∈ imgQ M U, ∃ w, u = hS.pbarRep a w - w} =
      {u | ∃ z : ↥M, (z : G) ∈ U ∧ ∃ w, u = SecMod.secConj hS.pbarHyp z w - w} := by
    ext u
    constructor
    · rintro ⟨a, ha, w, rfl⟩
      obtain ⟨z, hzU, rfl⟩ := mem_imgQ_iff.mp ha
      exact ⟨z, hzU, w, by rw [Sec6Hyp.pbarRep, secDescend_apply]⟩
    · rintro ⟨z, hzU, w, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 ↥M) z, mk_mem_imgQ hzU, w,
        by rw [Sec6Hyp.pbarRep, secDescend_apply]⟩
  rw [hset, span_secConj_eq hS.pbarHyp hUM]
  congr 1
  exact sup_eq_left.mpr (hS.sec5.V_le_commutator hU)

theorem Sec7Hyp.card_pbar (hS : Sec7Hyp M V n f) :
    Nat.card (SecMod hS.pbarHyp) = (2 ^ f) ^ (2 * n) := by
  letI := Sec6Hyp.pbarModule hS.toSec6Hyp
  have h := natCard_secMod hS.pbarHyp
  rw [hS.card_Pc, hS.card_V, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

end CFSG.RankThree.GF2n.Tim81
