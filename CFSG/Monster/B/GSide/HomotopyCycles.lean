module

public import CFSG.Monster.B.GSide.HomotopyLocal
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

private theorem isCycle_cons_of_isPath {u w : V} (h : G.Adj u w) (t : G.Walk w u)
    (ht : t.IsPath) (hlen : 2 ≤ t.length) : (Walk.cons h t).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨ht, ?_⟩
  cases t with
  | nil => simp at hlen
  | @cons _ x _ h' t' =>
    rw [Walk.cons_isPath_iff] at ht
    obtain ⟨ht', hw⟩ := ht
    have hxu : x ≠ u := by
      cases t' with
      | nil => simp at hlen
      | cons h'' t'' =>
        rw [Walk.cons_isPath_iff] at ht'
        exact fun hxu => ht'.2 (hxu ▸ t''.end_mem_support)
    rw [Walk.edges_cons, List.mem_cons, not_or]
    refine ⟨fun he => ?_, fun he => hw (t'.snd_mem_support_of_mem_edges he)⟩
    rcases Sym2.eq_iff.1 he with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact h.ne h₁
    · exact hxu h₁.symm

theorem homotopic_bypass [DecidableEq V] {L : ℕ}
    (hcyc : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≤ L → Homotopic c .nil)
    {u v : V} (p : G.Walk u v) (hp : p.length ≤ L) : Homotopic p p.bypass := by
  induction p with
  | nil => exact Homotopic.refl _
  | @cons u w v h p ih =>
    rw [Walk.length_cons] at hp
    have ih' := ih (by omega)
    simp only [Walk.bypass]
    split_ifs with hs
    · have htpath : (p.bypass.takeUntil u hs).IsPath := p.bypass_isPath.takeUntil hs
      have htlen : (p.bypass.takeUntil u hs).length ≤ p.length :=
        (p.bypass.length_takeUntil_le_length hs).trans p.length_bypass_le_length
      have hc : Homotopic (Walk.cons h (p.bypass.takeUntil u hs)) .nil := by
        rcases Nat.lt_or_ge (p.bypass.takeUntil u hs).length 2 with hlt | hge
        · exact homotopic_nil_of_length_le_three _ (by rw [Walk.length_cons]; omega)
        · exact hcyc _ _ (isCycle_cons_of_isPath h _ htpath hge) (by rw [Walk.length_cons]; omega)
      have h₂ := hc.append_right (p.bypass.dropUntil u hs)
      rw [Walk.cons_append, Walk.take_spec, Walk.nil_append] at h₂
      exact (ih'.cons h).trans h₂
    · exact ih'.cons h

theorem homotopic_nil_of_forall_isCycle {L : ℕ}
    (hcyc : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≤ L → Homotopic c .nil)
    {u : V} (p : G.Walk u u) (hp : p.length ≤ L) : Homotopic p .nil := by
  classical
  have h := homotopic_bypass hcyc p hp
  rwa [Walk.eq_nil_iff_nil.2 (Walk.isPath_iff_nil.1 p.bypass_isPath)] at h

end CFSG.Monster.B.GSide
