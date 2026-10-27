module

public import CFSG.Quasithin.Recognition.F4Small

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y]

noncomputable def ptsCard (c : α.Completion Y) : ℕ :=
  Nat.card {v : c.Γ // CosetGeom.vtype v = false}

theorem stv_xv_eq_range (c : α.Completion Y) : stv c c.xv = (f1 (c := c)).range :=
  le_antisymm (stv_xv_le_range_f1 c) (by
    rintro _ ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a))

theorem card_stv_xv (c : α.Completion Y) (hc : c.IsFaithful) :
    Nat.card (stv c c.xv) = Nat.card α.G1 := by
  rw [stv_xv_eq_range]
  exact (Nat.card_congr (MonoidHom.ofInjective (f1_injective c hc)).toEquiv).symm

theorem card_G0 (c : α.Completion Y) : Nat.card c.G0 = Nat.card Y := by
  have h : c.φ1.range ⊔ c.φ2.range = ⊤ := c.gen
  show Nat.card ↥(c.φ1.range ⊔ c.φ2.range) = Nat.card Y
  rw [h]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

theorem orbit_xv_eq (c : α.Completion Y) :
    MulAction.orbit c.G0 c.xv = {v : c.Γ | CosetGeom.vtype v = false} := by
  rw [CosetGeom.orbit_γ₀_eq_Γ0]
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hv
    cases v with
    | inl x => exact ⟨x, rfl⟩
    | inr y => exact absurd hv (by simp [CosetGeom.vtype])

theorem card_Y_eq (c : α.Completion Y) (hc : c.IsFaithful) :
    Nat.card Y = c.ptsCard * Nat.card α.G1 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer c.G0 c.xv)
  have e1 : Nat.card (c.G0 ⧸ MulAction.stabilizer c.G0 c.xv) = c.ptsCard := by
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer c.G0 c.xv), orbit_xv_eq]
    rfl
  have e2 : Nat.card ↥(MulAction.stabilizer c.G0 c.xv) = Nat.card α.G1 := card_stv_xv c hc
  rw [← card_G0 c, h, e1, e2]

theorem card_nbPaths_eq {Y' : Type w} [Group Y'] (c : α.Completion Y) (d : α.Completion Y')
    (hc : c.IsFaithful) (hd : d.IsFaithful) (n : ℕ) :
    Nat.card ↥(GPath.nbPaths c.graph c.xv n) = Nat.card ↥(GPath.nbPaths d.graph d.xv n) := by
  have e1 := (c.graphCovering hc).bijOn_nbPaths xhat n
  have e2 := (d.graphCovering hd).bijOn_nbPaths xhat n
  rw [Θ_xhat c hc] at e1
  rw [Θ_xhat d hd] at e2
  exact (Nat.card_congr (e1.equiv _)).symm.trans (Nat.card_congr (e2.equiv _))

section Counting

variable [Finite Y] {c : α.Completion Y} {m : ℕ} (F : Facts46 c m)

include F

omit [Finite Y] in
theorem Facts46.bijOn_sphere {n : ℕ} (hn : n < m) :
    Set.BijOn (fun p : GPath c.graph n => p n) (GPath.nbPaths c.graph c.xv n)
      (CosetGeom.sphere n c.xv) := by
  refine ⟨fun p hp => (F.uniq n hn c.xv p hp).1, fun p hp q hq hpq => ?_, fun v hv => ?_⟩
  · have hg : q.IsGeodesic := by
      show c.graph.dist (q 0) (q n) = n
      rw [hq.1]
      exact (F.uniq n hn c.xv q hq).1
    exact ((F.uniq n hn c.xv p hp).2 q hq.1 hpq.symm hg).symm
  · obtain ⟨P, h0, hPv, hnb⟩ := GPath.exists_geodesic' (connected_graph c) c.xv v (n := n) hv
    exact ⟨P, ⟨h0, hnb⟩, hPv⟩

omit [Finite Y] in
theorem Facts46.card_sphere_lt {n : ℕ} (hn : n < m) :
    Nat.card ↥(CosetGeom.sphere n c.xv) = Nat.card ↥(GPath.nbPaths c.graph c.xv n) :=
  (Nat.card_congr ((F.bijOn_sphere hn).equiv _)).symm

omit [Finite Y] in
theorem Facts46.card_nbPaths_m (hAll : ∀ a b : c.Γ, c.graph.dist a b = m → BijFirst c m a b) :
    Nat.card ↥(GPath.nbPaths c.graph c.xv m) =
      Nat.card ↥(CosetGeom.sphere m c.xv) * Nat.card ↥(CosetGeom.nbrs c.xv) := by
  have hm := F.hm
  have hsph : ∀ p : ↥(GPath.nbPaths c.graph c.xv m), p.1 m ∈ CosetGeom.sphere m c.xv :=
    fun p => F.dist_m c.xv p.1 p.2
  have hnbr : ∀ p : ↥(GPath.nbPaths c.graph c.xv m), p.1 1 ∈ CosetGeom.nbrs c.xv := by
    intro p
    show c.graph.Adj c.xv (p.1 1)
    have h0 : p.1 0 = c.xv := p.2.1
    have := p.1.adj 0 (by omega)
    rw [h0] at this
    exact this
  let Φ : ↥(GPath.nbPaths c.graph c.xv m) → ↥(CosetGeom.sphere m c.xv) × ↥(CosetGeom.nbrs c.xv) :=
    fun p => (⟨p.1 m, hsph p⟩, ⟨p.1 1, hnbr p⟩)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro p q h
      have h1 : p.1 m = q.1 m := congrArg (fun x => x.1.1) h
      have h2 : p.1 1 = q.1 1 := congrArg (fun x => x.2.1) h
      have hb : c.graph.dist c.xv (p.1 m) = m := F.dist_m c.xv p.1 p.2
      have hpm : p.1 ∈ c.geods m c.xv (p.1 m) := Facts46.mem_geods F p.2
      have hqm : q.1 ∈ c.geods m c.xv (p.1 m) := by
        have := Facts46.mem_geods F q.2
        rwa [← h1] at this
      exact Subtype.ext ((hAll _ _ hb).injOn hpm hqm h2)
    · rintro ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
      obtain ⟨t, ht, hty⟩ := (hAll c.xv b hb).surjOn hy
      have ht' := (Facts46.mem_geods_iff F).mp ht
      refine ⟨⟨t, ht'.1⟩, ?_⟩
      simp only [Φ, ht'.2, hty]
  rw [Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod]

noncomputable def ptsLe (c : α.Completion Y) (M : ℕ) : ℕ :=
  Nat.card {v : c.Γ // CosetGeom.vtype v = false ∧ c.graph.dist c.xv v ≤ M}

omit F in
theorem Facts46.card_ptsLe (M : ℕ) :
    c.ptsLe M = ∑ k ∈ Finset.range (M + 1),
      if Even k then Nat.card ↥(CosetGeom.sphere k c.xv) else 0 := by
  classical
  let _ : Fintype c.Γ := Fintype.ofFinite c.Γ
  have hpar : ∀ v : c.Γ, CosetGeom.vtype v = false ↔ Even (c.graph.dist c.xv v) := fun v => by
    have := GPath.dist_even_iff (connected_graph c) (fun _ _ h => CosetGeom.vtype_ne_of_adj h)
      c.xv v
    rw [← this]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact h.symm
  unfold ptsLe
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := fun v => c.graph.dist c.xv v)
      (t := Finset.range (M + 1))
      (fun v hv => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hv.2))]
  refine Finset.sum_congr rfl fun k hkM => ?_
  have hkM' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkM)
  by_cases hk : Even k
  · simp only [hk, ite_true]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show _ ↔ c.graph.dist c.xv v = k
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨⟨(hpar v).mpr (h ▸ hk), h ▸ hkM'⟩, h⟩
  · simp only [hk, ite_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    intro h
    exact hk (h ▸ (hpar v).mp hv.1)

omit F in
theorem Facts46.ptsLe_le (M : ℕ) : c.ptsLe M ≤ c.ptsCard := by
  unfold ptsLe ptsCard
  exact Nat.card_le_card_of_injective (fun v => ⟨v.1, v.2.1⟩) (fun a b h => by
    apply Subtype.ext
    exact congrArg (Subtype.val : {v : c.Γ // CosetGeom.vtype v = false} → c.Γ) h)

omit F in
theorem Facts46.ptsLe_lt (M : ℕ)
    (h : ∃ v : c.Γ, CosetGeom.vtype v = false ∧ M < c.graph.dist c.xv v) :
    c.ptsLe M < c.ptsCard := by
  obtain ⟨w, hw, hwd⟩ := h
  unfold ptsLe ptsCard
  have hfin : Finite {v : c.Γ // CosetGeom.vtype v = false} := inferInstance
  have hinj : Function.Injective (fun v : {v : c.Γ // CosetGeom.vtype v = false ∧
      c.graph.dist c.xv v ≤ M} => (⟨v.1, v.2.1⟩ : {v : c.Γ // CosetGeom.vtype v = false})) :=
    fun a b h => Subtype.ext
      (congrArg (Subtype.val : {v : c.Γ // CosetGeom.vtype v = false} → c.Γ) h)
  have hle := Nat.card_le_card_of_injective _ hinj
  refine lt_of_le_of_ne hle fun heq => ?_
  have hbij : Function.Bijective (fun v : {v : c.Γ // CosetGeom.vtype v = false ∧
      c.graph.dist c.xv v ≤ M} => (⟨v.1, v.2.1⟩ : {v : c.Γ // CosetGeom.vtype v = false})) :=
    (Function.Injective.bijective_of_nat_card_le hinj (le_of_eq heq.symm))
  obtain ⟨v, hv⟩ := hbij.2 ⟨w, hw⟩
  have := congrArg Subtype.val hv
  have hd : c.graph.dist c.xv w ≤ M := by
    have h2 : v.1 = w := this
    rw [← h2]
    exact v.2.2
  omega

omit F in
theorem Facts46.card_pts (hdiam : ∀ u v : c.Γ, c.graph.dist u v ≤ m) :
    c.ptsCard = ∑ k ∈ Finset.range (m + 1),
      if Even k then Nat.card ↥(CosetGeom.sphere k c.xv) else 0 := by
  rw [← Facts46.card_ptsLe (c := c) m]
  unfold ptsLe ptsCard
  exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
    constructor
    · intro h; exact ⟨h, hdiam _ _⟩
    · intro h; exact h.1)

omit [Finite Y] in
theorem Facts46.card_nbPaths_m_large (hl : c.IsLarge m) :
    Nat.card ↥(GPath.nbPaths c.graph c.xv m) = Nat.card ↥(CosetGeom.sphere m c.xv) := by
  have hsph : ∀ p : ↥(GPath.nbPaths c.graph c.xv m), p.1 m ∈ CosetGeom.sphere m c.xv :=
    fun p => F.dist_m c.xv p.1 p.2
  let Φ : ↥(GPath.nbPaths c.graph c.xv m) → ↥(CosetGeom.sphere m c.xv) :=
    fun p => ⟨p.1 m, hsph p⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro p q h
      have h1 : p.1 m = q.1 m := congrArg Subtype.val h
      have hp : p.1.IsGeodesic := (Facts46.mem_geods F p.2).2.2
      have hq : q.1.IsGeodesic := (Facts46.mem_geods F q.2).2.2
      exact Subtype.ext (hl p.1 q.1 hp hq (by rw [p.2.1, q.2.1]) h1)
    · rintro ⟨b, hb⟩
      obtain ⟨P, h0, hPb, hnb⟩ := GPath.exists_geodesic' (connected_graph c) c.xv b (n := m) hb
      exact ⟨⟨P, h0, hnb⟩, Subtype.ext hPb⟩
  exact Nat.card_congr (Equiv.ofBijective Φ hΦ)

end Counting

end RankTwoAmalgam.Completion

end CFSG.Quasithin
