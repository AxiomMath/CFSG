module

public import CFSG.Quasithin.Recognition.F4Small

public section

namespace CFSG.Quasithin.H13.F48Gen

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

variable {α : RankTwoAmalgam.{u}} {Y : Type} [Group Y] (c : α.Completion Y)
  (hc : c.IsFaithful)

theorem Θ_vtype (v : α.Γhat) : CosetGeom.vtype (c.Θ hc v) = CosetGeom.vtype v := by
  cases v <;> rfl

theorem hat_connected : α.graphHat.Connected := CosetGeom.connected rfl

theorem endpoint_eq {m : ℕ} (F : Facts46 c m) {n k : ℕ} (hn : n < m) (hk : k < m)
    {P : GPath α.graphHat n} {Q : GPath α.graphHat k}
    (hP : P ∈ GPath.nbPaths α.graphHat lhat n) (hQ : Q ∈ GPath.nbPaths α.graphHat lhat k)
    (h : c.Θ hc (P n) = c.Θ hc (Q k)) : n = k ∧ P n = Q k := by
  have hcov := c.graphCovering hc
  have hl : c.Θ hc lhat = c.lv := Θ_lhat c hc
  have hPm : hcov.pathMap P ∈ GPath.nbPaths c.graph c.lv n :=
    ⟨by rw [GraphCovering.pathMap_apply, hP.1, hl], (hcov.noBack_pathMap_iff P).2 hP.2⟩
  have hQm : hcov.pathMap Q ∈ GPath.nbPaths c.graph c.lv k :=
    ⟨by rw [GraphCovering.pathMap_apply, hQ.1, hl], (hcov.noBack_pathMap_iff Q).2 hQ.2⟩
  obtain ⟨hdP, hunP⟩ := F.uniq n hn c.lv _ hPm
  obtain ⟨hdQ, -⟩ := F.uniq k hk c.lv _ hQm
  have hz : hcov.pathMap P n = hcov.pathMap Q k := by
    simpa only [GraphCovering.pathMap_apply] using h
  have hnk : n = k := by rw [← hdP, ← hdQ, hz]
  subst hnk
  have hgeo : (hcov.pathMap Q).IsGeodesic := by
    show c.graph.dist ((hcov.pathMap Q) 0) ((hcov.pathMap Q) n) = n
    rw [hQm.1]
    exact hdQ
  have hQP : hcov.pathMap Q = hcov.pathMap P := hunP _ hQm.1 hz.symm hgeo
  have := (hcov.bijOn_nbPaths lhat n).injOn hQ hP hQP
  exact ⟨rfl, by rw [this]⟩

theorem Θ_inj_ball {m : ℕ} (F : Facts46 c m) {u v : α.Γhat}
    (hu : α.graphHat.dist lhat u ≤ m - 1) (hv : α.graphHat.dist lhat v ≤ m - 1)
    (h : c.Θ hc u = c.Θ hc v) : u = v := by
  have hm := F.hm
  obtain ⟨P, hP0, hPu, hPnb⟩ := GPath.exists_geodesic hat_connected lhat u
  obtain ⟨Q, hQ0, hQv, hQnb⟩ := GPath.exists_geodesic hat_connected lhat v
  have := endpoint_eq c hc F (n := α.graphHat.dist lhat u) (k := α.graphHat.dist lhat v)
    (by omega) (by omega) ⟨hP0, hPnb⟩ ⟨hQ0, hQnb⟩ (by rw [hPu, hQv]; exact h)
  rw [← hPu, ← hQv]
  exact this.2

theorem exists_lift_ball {n : ℕ} {z : c.Γ} (hz : c.graph.dist c.lv z ≤ n) :
    ∃ u : α.Γhat, α.graphHat.dist lhat u ≤ n ∧ c.Θ hc u = z := by
  have hcov := c.graphCovering hc
  obtain ⟨P, hP0, hPz, hPnb⟩ := GPath.exists_geodesic (connected_graph c) c.lv z
  have hl : c.Θ hc lhat = c.lv := Θ_lhat c hc
  obtain ⟨Q, hQ, hQP⟩ := (hcov.bijOn_nbPaths lhat (c.graph.dist c.lv z)).surjOn
    (show P ∈ GPath.nbPaths c.graph (c.Θ hc lhat) _ from ⟨by rw [hl]; exact hP0, hPnb⟩)
  refine ⟨Q (c.graph.dist c.lv z), ?_, ?_⟩
  · have := GPath.dist_le_length hat_connected Q
    rw [hQ.1] at this
    omega
  · have := congrArg (fun r : GPath c.graph _ => r (c.graph.dist c.lv z)) hQP
    simpa [hPz] using this

theorem dist_lv_le {m : ℕ} (hm : Even m) (hD : ∀ u v : c.Γ, c.graph.dist u v ≤ m) {z : c.Γ}
    (hz : CosetGeom.vtype z = false) : c.graph.dist c.lv z ≤ m - 1 := by
  have hpar := GPath.dist_even_iff (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) c.lv z
  have h1 : CosetGeom.vtype c.lv ≠ CosetGeom.vtype z := by
    show true ≠ _
    rw [hz]
    decide
  have h2 : ¬ Even (c.graph.dist c.lv z) := fun he => h1 (hpar.2 he)
  have h3 := hD c.lv z
  rcases Nat.lt_or_ge (c.graph.dist c.lv z) m with h | h
  · omega
  · have : c.graph.dist c.lv z = m := by omega
    exact absurd (this ▸ hm) h2

theorem exists_point_ball {m : ℕ} (hm : Even m) (hD : ∀ u v : c.Γ, c.graph.dist u v ≤ m)
    {z : c.Γ} (hz : CosetGeom.vtype z = false) :
    ∃ u : α.Γhat, CosetGeom.vtype u = false ∧ α.graphHat.dist lhat u ≤ m - 1 ∧ c.Θ hc u = z := by
  obtain ⟨u, hu, hΘ⟩ := exists_lift_ball c hc (dist_lv_le c hm hD hz)
  exact ⟨u, by rw [← Θ_vtype c hc u, hΘ, hz], hu, hΘ⟩

end CFSG.Quasithin.H13.F48Gen
