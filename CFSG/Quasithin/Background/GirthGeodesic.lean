module

public import CFSG.Quasithin.Background.F3Geodesic
public import Mathlib.Combinatorics.SimpleGraph.Girth

public section

namespace CFSG.Quasithin

open SimpleGraph

universe u

variable {V : Type u} {Γ : SimpleGraph V}

theorem eq_of_adj_of_dist_succ_of_le_egirth {m : ℕ} (hΓ : Γ.Connected)
    (hg : ((2 * m : ℕ) : ℕ∞) ≤ Γ.egirth) {y v z₁ z₂ : V} (hv : Γ.dist y v < m)
    (h₁ : Γ.Adj v z₁) (h₂ : Γ.Adj v z₂) (hd₁ : Γ.dist y z₁ + 1 = Γ.dist y v)
    (hd₂ : Γ.dist y z₂ + 1 = Γ.dist y v) : z₁ = z₂ := by
  by_contra hne
  obtain ⟨p₁, -, hl₁⟩ := hΓ.exists_path_of_dist z₁ y
  obtain ⟨p₂, -, hl₂⟩ := hΓ.exists_path_of_dist z₂ y
  have e₁ : Γ.dist z₁ y = Γ.dist y z₁ := SimpleGraph.dist_comm
  have e₂ : Γ.dist z₂ y = Γ.dist y z₂ := SimpleGraph.dist_comm
  have e₃ : Γ.dist v y = Γ.dist y v := SimpleGraph.dist_comm
  have hq₁ : (Walk.cons h₁ p₁).IsPath :=
    (Walk.cons h₁ p₁).isPath_of_length_eq_dist (by
      rw [Walk.length_cons, hl₁]
      omega)
  have hq₂ : (Walk.cons h₂ p₂).IsPath :=
    (Walk.cons h₂ p₂).isPath_of_length_eq_dist (by
      rw [Walk.length_cons, hl₂]
      omega)
  have hne' : Walk.cons h₁ p₁ ≠ Walk.cons h₂ p₂ := fun e => hne (by
    have := congrArg (fun q : Γ.Walk v y => q.getVert 1) e
    simpa [Walk.getVert_cons_succ] using this)
  obtain ⟨w, -, -, c, hc, hcl⟩ := hq₁.exists_isCycle_length_le_add_of_ne hq₂ hne'
  have h3 : 2 * m ≤ c.length := by
    have h4 : ((2 * m : ℕ) : ℕ∞) ≤ (c.length : ℕ∞) := le_trans hg hc.egirth_le_length
    exact ENat.natCast_le_natCast.mp h4
  simp only [Walk.length_cons] at hcl
  omega

theorem uniqueGeod_of_le_egirth {m : ℕ} (hΓ : Γ.Connected)
    (hg : ((2 * m : ℕ) : ℕ∞) ≤ Γ.egirth) : UniqueGeod Γ m := by
  intro n
  induction n with
  | zero =>
    intro p q _ _ hp0 _ _
    refine GPath.ext' fun i hi => ?_
    have hi0 : i = 0 := by omega
    subst hi0
    exact hp0
  | succ n ih =>
    intro p q hp hq hp0 hpn hn
    have hn1 : n ≤ n + 1 := by omega
    have hdpn : Γ.dist (p 0) (p n) = n :=
      GPath.dist_prefix hΓ p hp (i := n) (by omega)
    have hdqn' : Γ.dist (q 0) (q n) = n :=
      GPath.dist_prefix hΓ q hq (i := n) (by omega)
    have hdqn : Γ.dist (p 0) (q n) = n := by rwa [← hp0] at hdqn'
    have hmid : p n = q n :=
      eq_of_adj_of_dist_succ_of_le_egirth hΓ hg (y := p 0) (v := p (n + 1))
        (by rw [hp]; omega)
        (p.adj n (by omega)).symm
        (by simpa [hpn] using (q.adj n (by omega)).symm)
        (by rw [hdpn, hp])
        (by rw [hdqn, hp])
    have hpt : (p.take n hn1).IsGeodesic := by
      show Γ.dist (p.take n hn1 0) (p.take n hn1 n) = n
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n),
        GPath.take_apply_of_le _ _ _ le_rfl]
      exact hdpn
    have hqt : (q.take n hn1).IsGeodesic := by
      show Γ.dist (q.take n hn1 0) (q.take n hn1 n) = n
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n),
        GPath.take_apply_of_le _ _ _ le_rfl]
      exact hdqn'
    have h0t : (p.take n hn1) 0 = (q.take n hn1) 0 := by
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n),
        GPath.take_apply_of_le _ _ _ (Nat.zero_le n)]
      exact hp0
    have hnt : (p.take n hn1) n = (q.take n hn1) n := by
      rw [GPath.take_apply_of_le _ _ _ le_rfl,
        GPath.take_apply_of_le _ _ _ le_rfl]
      exact hmid
    have heq := ih (p.take n hn1) (q.take n hn1) hpt hqt h0t hnt (by omega)
    refine GPath.ext' fun i hi => ?_
    by_cases hin : i ≤ n
    · have h := congrArg (fun r : GPath Γ n => r i) heq
      rwa [GPath.take_apply_of_le _ _ _ hin,
        GPath.take_apply_of_le _ _ _ hin] at h
    · have hi' : i = n + 1 := by omega
      subst hi'
      exact hpn

end CFSG.Quasithin
