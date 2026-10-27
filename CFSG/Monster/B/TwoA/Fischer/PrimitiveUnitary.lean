module

public import CFSG.Monster.B.Classical.UnitarySixGraph
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix MulAction
open scoped Pointwise

theorem projAct_mem_block_of_rel {B : Set IsoPt}
    (hB : letI := MulAction.compHom IsoPt projAct; IsBlock ProjSU B)
    {p q x r : IsoPt} (hp : p ∈ B) (hq : q ∈ B) (hx : x ∈ B)
    (h : ∃ g : ProjSU, projAct g p = x ∧ projAct g q = r) : r ∈ B := by
  let _ := MulAction.compHom IsoPt projAct
  obtain ⟨g, hgp, hgq⟩ := h
  have hgB : g • B = B := hB.smul_eq_of_mem hp (show projAct g p ∈ B by rw [hgp]; exact hx)
  rw [← hgB, ← hgq]
  exact Set.smul_mem_smul_set hq

theorem isoGraph_exists_common_neighbor {p y : IsoPt} (hpy : p ≠ y) (h : ¬isoGraph.Adj p y) :
    ∃ z, isoGraph.Adj p z ∧ isoGraph.Adj y z := by
  have hc := isSRGWith.of_not_adj hpy h
  obtain ⟨z, hz⟩ : (isoGraph.commonNeighbors p y).Nonempty := by
    rw [← Set.nonempty_coe_sort, ← Fintype.card_pos_iff, hc]
    norm_num
  exact ⟨z, (isoGraph.mem_commonNeighbors.1 hz).1, (isoGraph.mem_commonNeighbors.1 hz).2⟩

theorem isoGraph_exists_adj_not_adj {p q : IsoPt} (hpq : p ≠ q) (h : ¬isoGraph.Adj p q) :
    ∃ r, isoGraph.Adj q r ∧ ¬isoGraph.Adj p r := by
  by_contra! hall
  have hsub : isoGraph.neighborSet q ⊆ isoGraph.commonNeighbors p q := fun r hr =>
    isoGraph.mem_commonNeighbors.2 ⟨hall r hr, hr⟩
  have hle := Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  rw [isSRGWith.of_not_adj hpq h, SimpleGraph.card_neighborSet_eq_degree,
    isSRGWith.regular q] at hle
  omega

theorem isPreprimitive_projAct :
    letI := MulAction.compHom IsoPt projAct
    IsPreprimitive ProjSU IsoPt := by
  let _ := MulAction.compHom IsoPt projAct
  have : IsPretransitive ProjSU IsoPt := ⟨fun p q => projAct_transitive p q⟩
  refine IsPreprimitive.mk fun {B} hB => ?_
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  right
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.1 hs
  have hadj : ∀ {p q : IsoPt}, p ∈ B → q ∈ B → isoGraph.Adj p q → B = Set.univ := by
    intro p q hp hq hpq
    have hcl : ∀ x r, x ∈ B → isoGraph.Adj x r → r ∈ B := fun x r hx hxr =>
      projAct_mem_block_of_rel hB hp hq hx (projAct_transitive_adj p q x r hpq hxr)
    refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : p = y
    · exact hy ▸ hp
    by_cases hpy : isoGraph.Adj p y
    · exact hcl p y hp hpy
    obtain ⟨z, hpz, hyz⟩ := isoGraph_exists_common_neighbor hy hpy
    exact hcl z y (hcl p z hp hpz) hyz.symm
  by_cases hpq' : isoGraph.Adj p q
  · exact hadj hp hq hpq'
  obtain ⟨r, hqr, hpr⟩ := isoGraph_exists_adj_not_adj hpq hpq'
  have hpr' : p ≠ r := fun e => hpq' (e ▸ hqr.symm)
  have hr : r ∈ B :=
    projAct_mem_block_of_rel hB hp hq hp (projAct_transitive_nonadj p q p r hpq hpq' hpr' hpr)
  exact hadj hq hr hqr

end CFSG.Monster.B.TwoA.Fischer
