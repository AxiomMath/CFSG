module

public import CFSG.Monster.B.Co2.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

theorem add_self_L2 (x : L2) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def shortGraph : SimpleGraph L2 where
  Adj a b := a ∈ shortSet ∧ b ∈ shortSet ∧ a + b ∈ shortSet
  symm := ⟨fun a b ⟨ha, hb, hab⟩ => ⟨hb, ha, by rwa [add_comm]⟩⟩
  loopless := ⟨fun a ⟨_, _, h⟩ => zero_notMem_shortSet (by rwa [add_self_L2] at h)⟩

theorem shortGraph_adj {a b : L2} :
    shortGraph.Adj a b ↔ a ∈ shortSet ∧ b ∈ shortSet ∧ a + b ∈ shortSet := Iff.rfl

theorem mem_shortSet_of_adj_right {a b : L2} (h : shortGraph.Adj a b) : b ∈ shortSet := h.2.1

theorem kOp_mem_shortSet_iff (k : OLq) {x : L2} : kOp k x ∈ shortSet ↔ x ∈ shortSet := by
  have h : ∀ (k : OLq) {x : L2}, x ∈ shortSet → kOp k x ∈ shortSet := by
    intro k x hx
    induction k using QuotientGroup.induction_on with
    | H g =>
      rw [kOp_mk]
      exact modTwoEnd_mem_shortSet g hx
  refine ⟨fun hx => ?_, h k⟩
  have := h k⁻¹ hx
  rwa [kOp_inv_apply] at this

theorem qL_kOp (k : OLq) (x : L2) : qL (kOp k x) = qL x := by
  induction k using QuotientGroup.induction_on with
  | H g =>
    rw [kOp_mk]
    exact qL_modTwoEnd g x

theorem kOp_mem_frameDelta_iff (k : OLq) {x : L2} : kOp k x ∈ frameDelta ↔ x ∈ frameDelta := by
  induction k using QuotientGroup.induction_on with
  | H g =>
    rw [kOp_mk]
    exact modTwoEnd_mem_frameDelta_iff g

theorem shortGraph_adj_kOp (k : OLq) {a b : L2} :
    shortGraph.Adj (kOp k a) (kOp k b) ↔ shortGraph.Adj a b := by
  rw [shortGraph_adj, shortGraph_adj, ← map_add, kOp_mem_shortSet_iff, kOp_mem_shortSet_iff,
    kOp_mem_shortSet_iff]

@[expose] def kOpHom (k : OLq) : shortGraph →g shortGraph where
  toFun x := kOp k x
  map_rel' h := (shortGraph_adj_kOp k).2 h

theorem qL_eq_zero_of_mem_shortSet {x : L2} (hx : x ∈ shortSet) : qL x = 0 :=
  shortSet_subset_singular hx

theorem qL_add_of_mem_shortSet {a b : L2} (ha : a ∈ shortSet) (hb : b ∈ shortSet) :
    qL (a + b) = bL a b := by
  rw [qL_add, qL_eq_zero_of_mem_shortSet ha, qL_eq_zero_of_mem_shortSet hb, zero_add, zero_add]

theorem shortSet_pair_trichotomy {a b : L2} (ha : a ∈ shortSet) (hb : b ∈ shortSet) (hab : a ≠ b) :
    shortGraph.Adj a b ∨ qL (a + b) = 1 ∨ a + b ∈ frameDelta := by
  by_cases hs : a + b ∈ shortSet
  · exact Or.inl ⟨ha, hb, hs⟩
  · refine Or.inr ?_
    by_cases hq : qL (a + b) = 0
    · refine Or.inr ⟨fun h => hab ?_, hq, hs⟩
      have h1 : a = a + b + b := by rw [add_assoc, add_self_L2, add_zero]
      rwa [h, zero_add] at h1
    · exact Or.inl ((show ∀ c : ZMod 2, c ≠ 0 → c = 1 by decide) _ hq)

end CFSG.Monster.Tri.Leech
