module

public import CFSG.Quasithin.Recognition.F4Apart
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

universe u

section Graph

variable {V : Type u} {Γ : SimpleGraph V}

@[expose] def burnsideF45_cons {n : ℕ} (u : V) (p : GPath Γ n) (h : Γ.Adj u (p 0)) :
    GPath Γ (n + 1) where
  toFun i := if i = 0 then u else p (i - 1)
  adj i hi := by
    rcases i with _ | i
    · simpa using h
    · have := p.adj i (by omega)
      simpa using this
  tail i hi := by
    have h1 : i ≠ 0 := by omega
    have h2 : n + 1 ≠ 0 := by omega
    simp only [h1, h2, if_false]
    rw [p.tail (i - 1) (by omega)]
    simp

@[simp] theorem burnsideF45_cons_zero {n : ℕ} (u : V) (p : GPath Γ n) (h : Γ.Adj u (p 0)) :
    burnsideF45_cons u p h 0 = u := by
  show (if (0 : ℕ) = 0 then u else p (0 - 1)) = u
  simp

@[simp] theorem burnsideF45_cons_succ {n : ℕ} (u : V) (p : GPath Γ n) (h : Γ.Adj u (p 0))
    (i : ℕ) : burnsideF45_cons u p h (i + 1) = p i := by
  show (if i + 1 = 0 then u else p (i + 1 - 1)) = p i
  simp

variable {m : ℕ} (hP : IsGenPolygon Γ m)
include hP

theorem burnsideF45_existsUnique_geod (u v : V) (h : Γ.dist u v < m) :
    ∃! q : GPath Γ (Γ.dist u v), q 0 = u ∧ q (Γ.dist u v) = v ∧ q.IsGeodesic := by
  obtain ⟨p, hp0, hpn, -⟩ := GPath.exists_geodesic hP.connected u v
  refine ⟨p, ⟨hp0, hpn, ?_⟩, ?_⟩
  · show Γ.dist (p 0) (p (Γ.dist u v)) = Γ.dist u v
    rw [hp0, hpn]
  · rintro q ⟨hq0, hqn, hq⟩
    exact hP.uniqueGeod _ q p hq (by show Γ.dist (p 0) (p _) = _; rw [hp0, hpn])
      (hq0.trans hp0.symm) (hqn.trans hpn.symm) h

theorem burnsideF45_dist_nbr_opp {u v w : V} (huv : Γ.dist u v = m) (hw : Γ.Adj u w) :
    Γ.dist w v = m - 1 := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have h := GPath.dist_adj_succ_or hP.connected hc v hw
  have hd := hP.diam_le v w
  rw [SimpleGraph.dist_comm (u := v) (v := u), huv, SimpleGraph.dist_comm (u := v)] at h
  rw [SimpleGraph.dist_comm] at hd
  omega

theorem burnsideF45_bijFirst (hm : 2 ≤ m) {u v : V} (huv : Γ.dist u v = m) :
    Set.BijOn (fun t : GPath Γ m => t 1) {t | t 0 = u ∧ t m = v ∧ t.IsGeodesic}
      (Γ.neighborSet u) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t ⟨ht0, -, -⟩
    show Γ.Adj u (t 1)
    rw [← ht0]
    exact t.adj 0 (by omega)
  · rintro t ⟨ht0, htm, ht⟩ t' ⟨ht0', htm', ht'⟩ h1
    by_contra hne
    exact (GPath.geod_first_last_ne hP.connected hP.uniqueGeod (by omega) ht ht'
      (ht0.trans ht0'.symm) (htm.trans htm'.symm) hne).1 h1
  · intro w hw
    have hw' : Γ.Adj u w := hw
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hd : Γ.dist w v = k := by
      have := burnsideF45_dist_nbr_opp hP huv hw'
      omega
    obtain ⟨r, hr0, hrk, -⟩ := GPath.exists_geodesic' hP.connected w v hd
    refine ⟨burnsideF45_cons u r (hr0 ▸ hw'), ⟨by simp, by simp [hrk], ?_⟩, by simp [hr0]⟩
    show Γ.dist (burnsideF45_cons u r _ 0) (burnsideF45_cons u r _ (k + 1)) = k + 1
    simp [hrk, huv]

theorem burnsideF45_apartments (hm : 2 ≤ m) {u v : V} (huv : Γ.dist u v = m) (S : Set V) :
    (u ∈ S ∧ v ∈ S ∧ IsPolygon Γ S (2 * m)) ↔
      ∃ q₁ ∈ {t : GPath Γ m | t 0 = u ∧ t m = v ∧ t.IsGeodesic},
        ∃ q₂ ∈ {t : GPath Γ m | t 0 = u ∧ t m = v ∧ t.IsGeodesic},
          q₁ ≠ q₂ ∧ S = q₁.verts ∪ q₂.verts := by
  obtain ⟨c, hc⟩ := hP.bipartite
  constructor
  · rintro ⟨hu, hv, hS⟩
    obtain ⟨p, q, hp, hq, hp0, hq0, hpm, hqm, hne, hSeq⟩ :=
      GPath.exists_arcs_of_polygon hP.connected hm hS hu hv huv
    refine ⟨p, ⟨hp0, hpm, hp⟩, q, ⟨hq0, hqm, hq⟩, hne, ?_⟩
    rw [hSeq, GPath.range_cycSeq (by omega) (hp0.trans hq0.symm) (hpm.trans hqm.symm)]
  · rintro ⟨p, ⟨hp0, hpm, hp⟩, q, ⟨hq0, hqm, hq⟩, hne, rfl⟩
    have h0 : p 0 = q 0 := hp0.trans hq0.symm
    have hmm : p m = q m := hpm.trans hqm.symm
    refine ⟨Or.inl ⟨0, Nat.zero_le _, hp0⟩, Or.inl ⟨m, le_rfl, hpm⟩, ?_⟩
    rw [← GPath.range_cycSeq (by omega) h0 hmm]
    exact GPath.polygon_of_two_geods hP.connected hc hP.uniqueGeod hm hp hq h0 hmm hne

end Graph

section Completion

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem burnsideF45_clause3 (c : α.Completion Y) {m : ℕ} (hP : IsGenPolygon c.graph m) :
    ∀ u v : c.Γ, c.graph.dist u v < m →
      ∃! q : GPath c.graph (c.graph.dist u v),
        q 0 = u ∧ q (c.graph.dist u v) = v ∧ q.IsGeodesic :=
  fun u v h => burnsideF45_existsUnique_geod hP u v h

theorem burnsideF45_bijFirst_completion (c : α.Completion Y) {m : ℕ} (hP : IsGenPolygon c.graph m)
    (hm : 2 ≤ m) {u v : c.Γ} (huv : c.graph.dist u v = m) :
    Set.BijOn (fun t : GPath c.graph m => t 1) (c.geods m u v) (CosetGeom.nbrs u) :=
  burnsideF45_bijFirst hP hm huv

theorem burnsideF45_clause4 (c : α.Completion Y) {m : ℕ} (hP : IsGenPolygon c.graph m)
    (hm : 2 ≤ m) :
    ∀ u v : c.Γ, c.graph.dist u v = m →
      Nat.card ↥(c.geods m u v) = Nat.card ↥(CosetGeom.nbrs u) ∧
      ∀ S : Set c.Γ, (u ∈ S ∧ v ∈ S ∧ c.IsApartment m S) ↔
        ∃ q₁ ∈ c.geods m u v, ∃ q₂ ∈ c.geods m u v, q₁ ≠ q₂ ∧
          S = pathVerts q₁ ∪ pathVerts q₂ := by
  intro u v huv
  refine ⟨Nat.card_congr ((burnsideF45_bijFirst_completion c hP hm huv).equiv _), fun S => ?_⟩
  exact burnsideF45_apartments hP hm huv S

end Completion

end CFSG.ASVolI
