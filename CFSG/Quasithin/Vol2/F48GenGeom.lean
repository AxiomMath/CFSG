module

public import CFSG.Quasithin.Vol2.F48GenBall

public section

namespace CFSG.Quasithin.H13.F48Gen

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

variable {α : RankTwoAmalgam.{u}}

abbrev Pt {Y : Type} [Group Y] (c : α.Completion Y) : Type :=
  ↥(c.φ1.range ⊔ c.φ2.range) ⧸ c.φ1.range.subgroupOf (c.φ1.range ⊔ c.φ2.range)

abbrev QH (α : RankTwoAmalgam.{u}) : Type u :=
  ↥(α.Ghat1 ⊔ α.Ghat2) ⧸ α.Ghat1.subgroupOf (α.Ghat1 ⊔ α.Ghat2)

@[expose] def Near (m : ℕ) {Y : Type} [Group Y] (c : α.Completion Y) (z : Pt c) : Prop :=
  c.graph.dist c.xv (Sum.inl z) ≤ m - 2

section Cov

variable {Y : Type} [Group Y] (c : α.Completion Y) (hc : c.IsFaithful)

@[expose] noncomputable def Θp (q : QH α) : Pt c :=
  Sum.elim id (fun _ => ((1 : c.G0) : Pt c)) (c.Θ hc (Sum.inl q))

theorem Θ_inl (q : QH α) : c.Θ hc (Sum.inl q) = Sum.inl (Θp c hc q) := by
  have hv := Θ_vtype c hc (Sum.inl q)
  rcases h : c.Θ hc (Sum.inl q) with z | y
  · simp [Θp, h]
  · rw [h] at hv
    simp [CosetGeom.vtype] at hv

theorem Θp_smul (g : ↥(α.Ghat1 ⊔ α.Ghat2)) (q : QH α) :
    Θp c hc (g • q) = c.theta0 hc g • Θp c hc q := by
  have h1 := c.Θ_smul hc g (Sum.inl q)
  rw [CosetGeom.smul_inl, Θ_inl, Θ_inl, CosetGeom.smul_inl] at h1
  exact Sum.inl_injective h1

theorem Θp_xi1 (a : α.G1) (q : QH α) : Θp c hc (α.xi1 a • q) = f1 (c := c) a • Θp c hc q := by
  rw [Θp_smul, theta0_xi1]

theorem Θp_xi2 (a : α.G2) (q : QH α) : Θp c hc (α.xi2 a • q) = f2 (c := c) a • Θp c hc q := by
  rw [Θp_smul, theta0_xi2]

end Cov

@[expose] def Ball (m : ℕ) (α : RankTwoAmalgam.{u}) : Set (QH α) :=
  {q | α.graphHat.dist lhat (Sum.inl q) ≤ m - 1}

@[expose] def NearH (m : ℕ) (α : RankTwoAmalgam.{u}) : Set (QH α) :=
  {q | α.graphHat.dist xhat (Sum.inl q) ≤ m - 2}

theorem NearH_subset_Ball {m : ℕ} (hm : 2 ≤ m) : NearH m α ⊆ Ball m α := by
  intro q hq
  have hadj : α.graphHat.Adj xhat lhat := CosetGeom.adj_γ₀_γ₁
  have h1 : α.graphHat.dist lhat xhat = 1 := by
    rw [SimpleGraph.dist_comm]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have h2 := hat_connected.dist_triangle (u := lhat) (v := xhat) (w := Sum.inl q)
  show α.graphHat.dist lhat (Sum.inl q) ≤ m - 1
  have : α.graphHat.dist xhat (Sum.inl q) ≤ m - 2 := hq
  omega

theorem xi1_mem_NearH {m : ℕ} (a : α.G1) {q : QH α} (hq : q ∈ NearH m α) :
    α.xi1 a • q ∈ NearH m α := by
  show α.graphHat.dist xhat (Sum.inl (α.xi1 a • q)) ≤ m - 2
  have h := CosetGeom.dist_smul (α.xi1 a) xhat (Sum.inl q)
  rw [xi1_smul_xhat, CosetGeom.smul_inl] at h
  rw [CosetGeom.dist] at h
  rw [h]
  exact hq

theorem xi2_mem_Ball {m : ℕ} (a : α.G2) {q : QH α} (hq : q ∈ Ball m α) :
    α.xi2 a • q ∈ Ball m α := by
  show α.graphHat.dist lhat (Sum.inl (α.xi2 a • q)) ≤ m - 1
  have h := CosetGeom.dist_smul (α.xi2 a) lhat (Sum.inl q)
  rw [xi2_smul_lhat, CosetGeom.smul_inl] at h
  rw [CosetGeom.dist] at h
  rw [h]
  exact hq

section Cov2

variable {Y : Type} [Group Y] (c : α.Completion Y) (hc : c.IsFaithful)

theorem dist_Θ_le (u v : α.Γhat) : c.graph.dist (c.Θ hc u) (c.Θ hc v) ≤ α.graphHat.dist u v := by
  obtain ⟨w, hw⟩ := hat_connected.exists_walk_length_eq_dist u v
  let φ : α.graphHat →g c.graph := ⟨c.Θ hc, fun {a b} h => (c.graphCovering hc).adj a b h⟩
  have := SimpleGraph.dist_le (w.map φ)
  rw [SimpleGraph.Walk.length_map, hw] at this
  exact this

theorem Near_Θp {m : ℕ} {q : QH α} (hq : q ∈ NearH m α) : Near m c (Θp c hc q) := by
  have h := dist_Θ_le c hc xhat (Sum.inl q)
  rw [Θ_xhat, Θ_inl] at h
  exact h.trans hq

theorem exists_lift_at (v : α.Γhat) {z : c.Γ} {n : ℕ} (hz : c.graph.dist (c.Θ hc v) z ≤ n) :
    ∃ u : α.Γhat, α.graphHat.dist v u ≤ n ∧ c.Θ hc u = z := by
  have hcov := c.graphCovering hc
  obtain ⟨P, hP0, hPz, hPnb⟩ := GPath.exists_geodesic (connected_graph c) (c.Θ hc v) z
  obtain ⟨Q, hQ, hQP⟩ := (hcov.bijOn_nbPaths v (c.graph.dist (c.Θ hc v) z)).surjOn
    (show P ∈ GPath.nbPaths c.graph (c.Θ hc v) _ from ⟨hP0, hPnb⟩)
  refine ⟨Q (c.graph.dist (c.Θ hc v) z), ?_, ?_⟩
  · have := GPath.dist_le_length hat_connected Q
    rw [hQ.1] at this
    omega
  · have := congrArg (fun r : GPath c.graph _ => r (c.graph.dist (c.Θ hc v) z)) hQP
    simpa [hPz] using this

theorem exists_Θp_near {m : ℕ} {z : Pt c} (hz : Near m c z) :
    ∃ q ∈ NearH m α, Θp c hc q = z := by
  obtain ⟨u, hu, hΘ⟩ := exists_lift_at c hc xhat (z := Sum.inl z) (n := m - 2)
    (by rw [Θ_xhat]; exact hz)
  have hv : CosetGeom.vtype u = false := by
    rw [← Θ_vtype c hc u, hΘ]
    rfl
  rcases u with q | y
  · refine ⟨q, hu, ?_⟩
    rw [Θ_inl] at hΘ
    exact Sum.inl_injective hΘ
  · simp [CosetGeom.vtype] at hv

end Cov2

section Main

variable {Y Y' : Type} [Group Y] [Group Y'] (c : α.Completion Y) (d : α.Completion Y')
  (hc : c.IsFaithful) (hd : d.IsFaithful)

theorem Θp_inj_ball {m : ℕ} (F : Facts46 c m) {q q' : QH α} (hq : q ∈ Ball m α)
    (hq' : q' ∈ Ball m α) (h : Θp c hc q = Θp c hc q') : q = q' := by
  have := Θ_inj_ball c hc F (u := Sum.inl q) (v := Sum.inl q') hq hq'
    (by rw [Θ_inl, Θ_inl, h])
  exact Sum.inl_injective this

theorem exists_Θp_ball {m : ℕ} (hm : Even m) (hD : ∀ u v : c.Γ, c.graph.dist u v ≤ m)
    (z : Pt c) : ∃ q ∈ Ball m α, Θp c hc q = z := by
  obtain ⟨u, hv, hu, hΘ⟩ := exists_point_ball c hc hm hD (z := Sum.inl z) rfl
  rcases u with q | y
  · refine ⟨q, hu, ?_⟩
    rw [Θ_inl] at hΘ
    exact Sum.inl_injective hΘ
  · simp [CosetGeom.vtype] at hv

@[expose] noncomputable def ballEquiv {m : ℕ} (hm : Even m) (F : Facts46 c m)
    (hD : ∀ u v : c.Γ, c.graph.dist u v ≤ m) : ↥(Ball m α) ≃ Pt c :=
  Equiv.ofBijective (fun q => Θp c hc q.1)
    ⟨fun _ _ h => Subtype.ext (Θp_inj_ball c hc F (Subtype.property _) (Subtype.property _) h),
      fun z => by
        obtain ⟨q, hq, hz⟩ := exists_Θp_ball c hc hm hD z
        exact ⟨⟨q, hq⟩, hz⟩⟩

variable {m : ℕ} (hm : Even m) (Fc : Facts46 c m) (Fd : Facts46 d m)
  (Dc : ∀ u v : c.Γ, c.graph.dist u v ≤ m) (Dd : ∀ u v : d.Γ, d.graph.dist u v ≤ m)

@[expose] noncomputable def ptEquiv : Pt c ≃ Pt d :=
  (ballEquiv c hc hm Fc Dc).symm.trans (ballEquiv d hd hm Fd Dd)

theorem ptEquiv_Θp {q : QH α} (hq : q ∈ Ball m α) :
    ptEquiv c d hc hd hm Fc Fd Dc Dd (Θp c hc q) = Θp d hd q := by
  unfold ptEquiv
  rw [Equiv.trans_apply]
  have : (ballEquiv c hc hm Fc Dc).symm (Θp c hc q) = ⟨q, hq⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

theorem ptEquiv_f2 (a : α.G2) (z : Pt c) :
    ptEquiv c d hc hd hm Fc Fd Dc Dd (f2 (c := c) a • z) =
      f2 (c := d) a • ptEquiv c d hc hd hm Fc Fd Dc Dd z := by
  obtain ⟨q, hq, rfl⟩ := exists_Θp_ball c hc hm Dc z
  rw [← Θp_xi2, ptEquiv_Θp c d hc hd hm Fc Fd Dc Dd (xi2_mem_Ball a hq),
    ptEquiv_Θp c d hc hd hm Fc Fd Dc Dd hq, Θp_xi2]

theorem ptEquiv_f1 (a : α.G1) (z : Pt c) (hz : Near m c z) :
    ptEquiv c d hc hd hm Fc Fd Dc Dd (f1 (c := c) a • z) =
      f1 (c := d) a • ptEquiv c d hc hd hm Fc Fd Dc Dd z := by
  obtain ⟨q, hq, rfl⟩ := exists_Θp_near c hc hz
  rw [← Θp_xi1, ptEquiv_Θp c d hc hd hm Fc Fd Dc Dd
      (NearH_subset_Ball Fc.hm (xi1_mem_NearH a hq)),
    ptEquiv_Θp c d hc hd hm Fc Fd Dc Dd (NearH_subset_Ball Fc.hm hq), Θp_xi1]

theorem ptEquiv_near (z : Pt c) :
    Near m d (ptEquiv c d hc hd hm Fc Fd Dc Dd z) ↔ Near m c z := by
  constructor
  · intro h
    obtain ⟨q, hq, hqz⟩ := exists_Θp_near d hd h
    have hB := NearH_subset_Ball Fc.hm hq
    have e : ptEquiv c d hc hd hm Fc Fd Dc Dd (Θp c hc q) =
        ptEquiv c d hc hd hm Fc Fd Dc Dd z := by
      rw [ptEquiv_Θp c d hc hd hm Fc Fd Dc Dd hB, hqz]
    have := (ptEquiv c d hc hd hm Fc Fd Dc Dd).injective e
    rw [← this]
    exact Near_Θp c hc hq
  · intro h
    obtain ⟨q, hq, rfl⟩ := exists_Θp_near c hc h
    rw [ptEquiv_Θp c d hc hd hm Fc Fd Dc Dd (NearH_subset_Ball Fc.hm hq)]
    exact Near_Θp d hd hq

end Main

end CFSG.Quasithin.H13.F48Gen
