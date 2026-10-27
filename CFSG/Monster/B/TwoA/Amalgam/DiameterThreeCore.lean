module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoInst

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def DistThreeLocalOrbits :
    Prop :=
  ∀ v u : CVert, cgraph.dist v u = 3 →
    (cgraph.induce (cgraph.neighborSet u)).Connected ∧
    (cgraph.neighborSet u ∩ sphereFour v).Nonempty ∧
    (cgraph.neighborSet u \ sphereFour v).Nonempty ∧
    (∀ y ∈ cgraph.neighborSet u \ sphereFour v, ∀ y' ∈ cgraph.neighborSet u \ sphereFour v,
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u ∧ cvMul y s = y') ∧
    (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 ∧
    (cgraph.neighborSet u \ sphereFour v).ncard = 69615

section Core

variable (hloc : DistThreeLocalOrbits)
  (hno : ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → cgraph.dist v u ≠ 3)

include hloc in
theorem exists_adj_mem_X {v u : CVert} (hvu : cgraph.dist v u = 3) {y : CVert}
    (hy : y ∈ cgraph.neighborSet u \ sphereFour v) :
    ∃ x ∈ cgraph.neighborSet u ∩ sphereFour v, cgraph.Adj y x := by
  obtain ⟨hconn, ⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, htr, -, -⟩ := hloc v u hvu
  have hedge : ∃ a ∈ cgraph.neighborSet u \ sphereFour v,
      ∃ b ∈ cgraph.neighborSet u ∩ sphereFour v, cgraph.Adj a b := by
    by_contra hnone
    push Not at hnone
    have hreach := hconn.preconnected ⟨y₀, hy₀.1⟩ ⟨x₀, hx₀.1⟩
    obtain ⟨p⟩ := hreach
    have : ∀ (a b : cgraph.neighborSet u) (q : (cgraph.induce (cgraph.neighborSet u)).Walk a b),
        (a : CVert) ∉ sphereFour v → (b : CVert) ∉ sphereFour v := by
      intro a b q
      induction q with
      | nil => exact id
      | @cons a c b hac q ih =>
        intro ha
        apply ih
        intro hc
        exact hnone a ⟨a.2, ha⟩ c ⟨c.2, hc⟩ hac
    exact this _ _ p hy₀.2 hx₀.2
  obtain ⟨a, ha, b, hb, hab⟩ := hedge
  obtain ⟨s, hsv, hsu, hsy⟩ := htr a ha y hy
  refine ⟨cvMul b s, ⟨?_, mem_sphereFour_of_cvMul hsv hb.2⟩, ?_⟩
  · have h := (cgraph_adj_cvMul u b s).2 hb.1
    rwa [hsu] at h
  · have h := (cgraph_adj_cvMul a b s).2 hab
    rwa [hsy] at h

include hloc hno in
theorem dist_of_adj_of_dist_three
    {v u y : CVert} (hvu : cgraph.dist v u = 3)
    (huy : cgraph.Adj u y) :
    (y ∈ sphereFour v ∨ cgraph.dist v y = 3) ∧ (y ∉ sphereFour v → cgraph.dist v y = 3) := by
  have hY : y ∉ sphereFour v → cgraph.dist v y = 3 := by
    intro hy4
    obtain ⟨x, hx, hyx⟩ := exists_adj_mem_X hloc hvu ⟨huy, hy4⟩
    have hle : cgraph.dist v y ≤ 3 := by
      have h := cgraph_connected.dist_triangle (u := v) (v := x) (w := y)
      rw [hx.2.1, SimpleGraph.dist_comm (u := x), SimpleGraph.dist_eq_one_iff_adj.2 hyx] at h
      omega
    have hge : 2 ≤ cgraph.dist v y := by
      have h := cgraph_connected.dist_triangle (u := v) (v := y) (w := u)
      rw [hvu, SimpleGraph.dist_comm (u := y), SimpleGraph.dist_eq_one_iff_adj.2 huy] at h
      omega
    rcases (show cgraph.dist v y = 2 ∨ cgraph.dist v y = 3 by omega) with h2 | h3
    ·
      exfalso
      rcases (labelThree_or_labelFour_of_dist exists_rootModel h2) with h3' | h4'
      · exact hno v y u ⟨h2, h3'.1⟩ huy.symm hvu
      · exact hy4 ⟨h2, h4'.1⟩
    · exact h3
  refine ⟨?_, hY⟩
  by_cases hy4 : y ∈ sphereFour v
  · exact Or.inl hy4
  · exact Or.inr (hY hy4)

include hloc hno in
theorem dist_le_three
    (v w : CVert) : cgraph.dist v w ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have hd4 : ∃ y z : CVert, cgraph.dist v y = 3 ∧ cgraph.Adj y z ∧ cgraph.dist v z = 4 := by
    obtain ⟨q, hq⟩ := (cgraph_connected.preconnected v w).exists_walk_length_eq_dist
    set z := q.getVert 4
    set y := q.getVert 3
    have hz : cgraph.dist v z = 4 := by
      have hzle : cgraph.dist v z ≤ 4 := by
        have := SimpleGraph.dist_le (q.take 4)
        simpa [z, SimpleGraph.Walk.take_length, min_eq_left (by omega : 4 ≤ q.length)] using this
      have hzge : 4 ≤ cgraph.dist v z := by
        have h1 := cgraph_connected.dist_triangle (u := v) (v := z) (w := w)
        have h2 : cgraph.dist z w ≤ q.length - 4 := by
          have := SimpleGraph.dist_le (q.drop 4)
          simpa [z, SimpleGraph.Walk.drop_length] using this
        omega
      omega
    have hy : cgraph.dist v y = 3 := by
      have hyle : cgraph.dist v y ≤ 3 := by
        have := SimpleGraph.dist_le (q.take 3)
        simpa [y, SimpleGraph.Walk.take_length, min_eq_left (by omega : 3 ≤ q.length)] using this
      have hyz : cgraph.Adj y z := by
        have := q.adj_getVert_succ (i := 3) (by omega)
        simpa [y, z] using this
      have h1 := cgraph_connected.dist_triangle (u := v) (v := y) (w := z)
      rw [hz, SimpleGraph.dist_eq_one_iff_adj.2 hyz] at h1
      omega
    refine ⟨y, z, hy, ?_, hz⟩
    have := q.adj_getVert_succ (i := 3) (by omega)
    simpa [y, z] using this
  obtain ⟨y, z, hy, hyz, hz⟩ := hd4
  rcases (dist_of_adj_of_dist_three hloc hno hy hyz).1 with h4 | h3
  · rw [h4.1] at hz
    omega
  · rw [h3] at hz
    omega

end Core

end CFSG.Monster.B.TwoA.Amalgam
