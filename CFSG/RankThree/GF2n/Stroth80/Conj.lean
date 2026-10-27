module

public import CFSG.RankThree.GF2n.Stroth80.Ctx
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem normalizer_conj_aux (g : G) (X : Subgroup G) :
    Subgroup.normalizer (conjSubgroup g X : Set G) =
      conjSubgroup g (Subgroup.normalizer (X : Set G)) :=
  (Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.conj g).toMonoidHom) X
    (MulAut.conj g).bijective).symm

private theorem inSubgroup_gF_conj (N : Subgroup G) (g : G) :
    inSubgroup generalizedFitting (conjSubgroup g N) =
      conjSubgroup g (inSubgroup generalizedFitting N) := by
  let e : ↥N ≃* ↥(conjSubgroup g N) := MulEquiv.subgroupMap (MulAut.conj g) N
  have key := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  show (generalizedFitting ↥(conjSubgroup g N)).map (conjSubgroup g N).subtype =
    ((generalizedFitting ↥N).map N.subtype).map (MulAut.conj g).toMonoidHom
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1 <;> ext x <;> rfl

private theorem fitting_eq_of_ctx (hc : Ctx M Q Z B) :
    inSubgroup generalizedFitting M = Q := by
  rw [hc.hyp.hQ]
  unfold inSubgroup
  rw [hc.hyp.fitting]

private theorem Q_le_M_of_ctx (hc : Ctx M Q Z B) : Q ≤ M := by
  rw [hc.hyp.hQ]
  unfold inSubgroup
  exact Subgroup.map_subtype_le _

private theorem normalizer_Z_eq (hc : Ctx M Q Z B) :
    Subgroup.normalizer (Z : Set G) = M := by
  have hZne : Z ≠ ⊥ := by
    intro h
    have h4 := hc.hyp.q4
    rw [h, Subgroup.card_bot] at h4
    omega
  have hZ2 : IsPGroup 2 Z := fun x =>
    ⟨1, Subtype.ext (by simpa using hc.hyp.toHyp79.sq_eq_one x x.2)⟩
  have hloc : IsPLocal 2 (Subgroup.normalizer (Z : Set G)) := ⟨Z, hZne, hZ2, rfl⟩
  have hle : M ≤ Subgroup.normalizer (Z : Set G) := hc.hyp.maxAb.prop.2.1
  by_contra hne
  exact hc.hyp.maxLocal.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) hloc

private theorem Z_le_conj_Q (hc : Ctx M Q Z B) {g : G}
    (hg : B = conjSubgroup g Z) : Z ≤ conjSubgroup g Q := by
  have hgV : conjSubgroup g Z ≠ Z := by
    rw [← hg]
    exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by
    rw [← hg]
    exact hc.le
  exact ((hc.hyp.toHyp79.toHyp218 hgV hgQ).conclusions hc.hyp.toHyp79.q4 rfl).1

theorem Ctx.inf_eq_bot (hc : Ctx M Q Z B) : Z ⊓ B = ⊥ := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [hg]
  refine inf_conjSubgroup_eq_bot_of_isTI hc.hyp.ti ?_
  rw [← hg]
  exact hc.ne

theorem Ctx.QB_eq (hc : Ctx M Q Z B) {g : G}
    (hg : B = conjSubgroup g Z) :
    Subgroup.normalizer (B : Set G) = conjSubgroup g M ∧ QB B = conjSubgroup g Q := by
  have hN : Subgroup.normalizer (B : Set G) = conjSubgroup g M := by
    rw [hg, normalizer_conj_aux, normalizer_Z_eq hc]
  refine ⟨hN, ?_⟩
  unfold QB
  rw [hN, inSubgroup_gF_conj, fitting_eq_of_ctx hc]

theorem Ctx.Z_le_QB (hc : Ctx M Q Z B) : Z ≤ QB B ∧ B ≤ M := by
  obtain ⟨g, hg⟩ := hc.conj
  refine ⟨?_, hc.le.trans (Q_le_M_of_ctx hc)⟩
  rw [(Ctx.QB_eq hc hg).2]
  exact Z_le_conj_Q hc hg

theorem Ctx.QB_inf_M_le (hc : Ctx M Q Z B) :
    QB B ⊓ M ≤ Subgroup.centralizer (Z : Set G) := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [(Ctx.QB_eq hc hg).2]
  intro x hx
  obtain ⟨hxQ, hxM⟩ := Subgroup.mem_inf.mp hx
  have hxN : x ∈ Subgroup.normalizer (Z : Set G) := by
    rw [normalizer_Z_eq hc]
    exact hxM
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzZ : z ∈ Z := hz
  have hzQ : z ∈ conjSubgroup g Q := Z_le_conj_Q hc hg hzZ
  have hcomm : ⁅x, z⁆ ∈ B := by
    rw [hg]
    exact hc.hyp.toHyp79.comm_mem_conj g hxQ hzQ
  have hconj : x * z * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hxN z).mp hz
  have hcomZ : ⁅x, z⁆ ∈ Z := by
    rw [commutatorElement_def]
    exact mul_mem hconj (inv_mem hzZ)
  have h1 : ⁅x, z⁆ = 1 := by
    have hmem : ⁅x, z⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hcomZ, hcomm⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

end CFSG.RankThree.GF2n.Stroth80
