module

public import CFSG.Monster.GMS.RonanTriangulable
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

theorem setOf_adj_dist_eq_one (a b : V) :
    {c | G.Adj a c ∧ G.dist c b = 1} = G.commonNeighbors a b := by
  ext c
  rw [Set.mem_ofPred_eq, SimpleGraph.mem_commonNeighbors, SimpleGraph.dist_eq_one_iff_adj,
    G.adj_comm c b]

theorem exists_adj_adj_of_dist_eq_two {a b : V} (h : G.dist a b = 2) :
    ∃ c, G.Adj a c ∧ G.Adj c b := by
  obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (G := G) (u := a) (v := b) (by omega)
  rw [h] at hq
  cases q with
  | nil => simp at hq
  | cons h₁ q =>
    cases q with
    | nil => simp at hq
    | cons h₂ q =>
      cases q with
      | nil => exact ⟨_, h₁, h₂⟩
      | cons _ _ => simp at hq

theorem dist_eq_two_of_adj_of_adj {a b c h : V} (hab : G.dist a b = 3) (hac : G.Adj a c)
    (hch : G.Adj c h) (hhb : G.Adj h b) : G.dist c b = 2 := by
  obtain ⟨p, hp⟩ := (hch.reachable.trans hhb.reachable).exists_walk_length_eq_dist
  have h₁ : G.dist a b ≤ (Walk.cons hac p).length := SimpleGraph.dist_le _
  have h₂ : G.dist c b ≤ (Walk.cons hch (Walk.cons hhb Walk.nil)).length := SimpleGraph.dist_le _
  rw [Walk.length_cons, hp] at h₁
  simp only [Walk.length_cons, Walk.length_nil] at h₂
  omega

theorem triangulable_of_dist_le_three (hD : ∀ x y : V, G.dist x y ≤ 3)
    (h2 : ∀ v w : V, G.dist v w = 2 → (G.induce (G.commonNeighbors v w)).Preconnected)
    (h2t : ∀ v x y : V, G.dist v x = 2 → G.dist v y = 2 → G.Adj x y →
      ∃ c, G.Adj v c ∧ G.Adj c x ∧ G.Adj c y)
    (h3 : ∀ v u : V, G.dist v u = 3 →
      (G.induce {c | G.Adj u c ∧ G.dist v c = 2}).Preconnected)
    (h3t : ∀ v x y : V, G.dist v x = 3 → G.dist v y = 3 → G.Adj x y →
      ∃ h, G.dist v h = 2 ∧ G.Adj h x ∧ G.Adj h y) :
    Triangulable G := by
  refine CFSG.Monster.GMS.triangulable_of_ronan hD (fun i hi hi' a b hab => ?_)
    (fun i hi hi' a b g hab hag hbg => ?_)
  · interval_cases i
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 1}).Preconnected
      rw [setOf_adj_dist_eq_one]
      exact h2 a b hab
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 2}).Preconnected
      have e : {c | G.Adj a c ∧ G.dist c b = 2} = {c | G.Adj a c ∧ G.dist b c = 2} := by
        ext c
        exact and_congr_right fun _ => by rw [SimpleGraph.dist_comm]
      rw [e]
      exact h3 b a (by rwa [SimpleGraph.dist_comm])
  · interval_cases i
    · obtain ⟨c, hac, hcb, hcg⟩ := h2t a b g hab hag hbg
      exact ⟨c, c, hac, SimpleGraph.dist_eq_one_iff_adj.2 hcb, hac,
        SimpleGraph.dist_eq_one_iff_adj.2 hcg, Or.inl rfl⟩
    · obtain ⟨h, hah, hhb, hhg⟩ := h3t a b g hab hag hbg
      obtain ⟨c, hac, hch⟩ := exists_adj_adj_of_dist_eq_two hah
      exact ⟨c, c, hac, dist_eq_two_of_adj_of_adj hab hac hch hhb, hac,
        dist_eq_two_of_adj_of_adj hag hac hch hhg, Or.inl rfl⟩

theorem triangulable_of_dist_le_three_weak (hD : ∀ x y : V, G.dist x y ≤ 3)
    (h2 : ∀ v w : V, G.dist v w = 2 → (G.induce (G.commonNeighbors v w)).Preconnected)
    (h2t : ∀ v x y : V, G.dist v x = 2 → G.dist v y = 2 → G.Adj x y →
      ∃ c c', G.Adj v c ∧ G.Adj c x ∧ G.Adj v c' ∧ G.Adj c' y ∧ (c = c' ∨ G.Adj c c'))
    (h3 : ∀ v u : V, G.dist v u = 3 →
      (G.induce {c | G.Adj u c ∧ G.dist v c = 2}).Preconnected)
    (h3t : ∀ v x y : V, G.dist v x = 3 → G.dist v y = 3 → G.Adj x y →
      ∃ h, G.dist v h = 2 ∧ G.Adj h x ∧ G.Adj h y) :
    Triangulable G := by
  refine CFSG.Monster.GMS.triangulable_of_ronan hD (fun i hi hi' a b hab => ?_)
    (fun i hi hi' a b g hab hag hbg => ?_)
  · interval_cases i
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 1}).Preconnected
      rw [setOf_adj_dist_eq_one]
      exact h2 a b hab
    · show (G.induce {c | G.Adj a c ∧ G.dist c b = 2}).Preconnected
      have e : {c | G.Adj a c ∧ G.dist c b = 2} = {c | G.Adj a c ∧ G.dist b c = 2} := by
        ext c
        exact and_congr_right fun _ => by rw [SimpleGraph.dist_comm]
      rw [e]
      exact h3 b a (by rwa [SimpleGraph.dist_comm])
  · interval_cases i
    · obtain ⟨c, c', hac, hcb, hac', hc'g, hcc'⟩ := h2t a b g hab hag hbg
      exact ⟨c, c', hac, SimpleGraph.dist_eq_one_iff_adj.2 hcb, hac',
        SimpleGraph.dist_eq_one_iff_adj.2 hc'g, hcc'⟩
    · obtain ⟨h, hah, hhb, hhg⟩ := h3t a b g hab hag hbg
      obtain ⟨c, hac, hch⟩ := exists_adj_adj_of_dist_eq_two hah
      exact ⟨c, c, hac, dist_eq_two_of_adj_of_adj hab hac hch hhb, hac,
        dist_eq_two_of_adj_of_adj hag hac hch hhg, Or.inl rfl⟩

end CFSG.Monster.B.GSide
