module

public import CFSG.Quasithin.Recognition.F4Count

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}
  (F : Facts46 c m)

include F

theorem Facts46.diam_le (hs : c.IsSmall m) (u v : c.Γ) : c.graph.dist u v ≤ m := by
  have hm := F.hm
  by_contra hlt
  have hlt' : m < c.graph.dist u v := not_le.mp hlt
  obtain ⟨P, hP0, hPv, -⟩ := GPath.exists_geodesic (connected_graph c) u v
  have hgeo : c.graph.dist (P 0) (P (c.graph.dist u v)) = c.graph.dist u v := by
    rw [hP0, hPv]
  have hw : c.graph.dist u (P m) = m := by
    have := GPath.dist_prefix (connected_graph c) P hgeo (show m ≤ c.graph.dist u v by omega)
    rwa [hP0] at this
  have hz : c.graph.dist u (P (m + 1)) = m + 1 := by
    have := GPath.dist_prefix (connected_graph c) P hgeo (show m + 1 ≤ c.graph.dist u v by omega)
    rwa [hP0] at this
  have hadj : c.graph.Adj (P m) (P (m + 1)) := P.adj m (by omega)
  have hbij := F.allBij hs (a := P m) (b := u) (by rw [SimpleGraph.dist_comm]; exact hw)
  obtain ⟨s, hs', hs1⟩ := hbij.2.2 (show P (m + 1) ∈ CosetGeom.nbrs (P m) from hadj)
  have hs1' : s 1 = P (m + 1) := hs1
  have hsg : s.IsGeodesic := hs'.2.2
  have hd := (hsg.drop (connected_graph c) 1 (by omega : 1 ≤ m))
  have hd' : c.graph.dist (s 1) (s m) = m - 1 := by
    have := hd
    unfold GPath.IsGeodesic at this
    rwa [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ le_rfl,
      show 1 + (m - 1) = m by omega, add_zero] at this
  rw [hs1', hs'.2.1, SimpleGraph.dist_comm, hz] at hd'
  omega

theorem Facts46.isGenPolygon (hs : c.IsSmall m) : IsGenPolygon c.graph m := by
  have hm := F.hm
  refine ⟨connected_graph c, ⟨CosetGeom.vtype, fun _ _ h => CosetGeom.vtype_ne_of_adj h⟩,
    F.diam_le hs, ?_, F.uniqueGeod, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := GPath.exists_nbPaths F.hval c.xv m
    exact ⟨c.xv, P m, F.dist_m c.xv P hP⟩
  · obtain ⟨p, q, hp, hq, h0, hmm, hne⟩ : ∃ p q : GPath c.graph m, p.IsGeodesic ∧ q.IsGeodesic ∧
        p 0 = q 0 ∧ p m = q m ∧ p ≠ q := by
      by_contra h
      apply hs
      intro p q hp hq h0 hmm
      by_contra hne
      exact h ⟨p, q, hp, hq, h0, hmm, hne⟩
    exact ⟨_, GPath.polygon_of_two_geods (connected_graph c)
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) F.uniqueGeod hm hp hq h0 hmm hne⟩
  · intro v
    obtain ⟨y₁, y₂, h1, h2, hne⟩ := F.exists_two_nbrs v
    have hsub : ({y₁, y₂} : Set c.Γ) ⊆ c.graph.neighborSet v := by
      intro y hy
      rcases hy with rfl | rfl
      · exact h1
      · exact h2
    calc (2 : ℕ∞) = ({y₁, y₂} : Set c.Γ).encard := (Set.encard_pair hne).symm
      _ ≤ (c.graph.neighborSet v).encard := Set.encard_le_encard hsub

omit [Finite Y] in
theorem Facts46.isSmall_of_polygon {S : Set c.Γ} (hS : IsPolygon c.graph S (2 * m)) :
    c.IsSmall m := by
  have hm := F.hm
  obtain ⟨e⟩ := hS
  have hM : 3 ≤ 2 * m := by omega
  have hpos : 0 < 2 * m := by omega
  let z : ℕ → c.Γ := fun i => (e ⟨i % (2 * m), Nat.mod_lt _ hpos⟩ : S).1
  have hper : ∀ i, z (i + 2 * m) = z i := fun i => by simp only [z, Nat.add_mod_right]
  have hadj : ∀ i, c.graph.Adj (z i) (z (i + 1)) := by
    intro i
    have h1 : (SimpleGraph.cycleGraph (2 * m)).Adj ⟨i % (2 * m), Nat.mod_lt _ hpos⟩
        ⟨(i + 1) % (2 * m), Nat.mod_lt _ hpos⟩ := by
      rw [cycleGraph_adj_iff hM]
      simp only []
      rcases Nat.lt_or_ge (i % (2 * m) + 1) (2 * m) with h | h
      · left
        rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega), Nat.mod_eq_of_lt h]
      · right; right; right
        have e1 : i % (2 * m) = 2 * m - 1 := by have := Nat.mod_lt i hpos; omega
        refine ⟨?_, e1⟩
        rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega)]
        have : i % (2 * m) + 1 = 2 * m := by omega
        rw [this]
        simp
    have := e.map_adj_iff.mpr h1
    exact this
  have hnb : ∀ i, z i ≠ z (i + 2) := by
    intro i h
    have h1 : e ⟨i % (2 * m), Nat.mod_lt _ hpos⟩ = e ⟨(i + 2) % (2 * m), Nat.mod_lt _ hpos⟩ :=
      Subtype.ext h
    have h2 := e.injective h1
    have h3 : i % (2 * m) = (i + 2) % (2 * m) := congrArg Fin.val h2
    have h4 : (2 * m) ∣ 2 := by
      have h5 := Nat.sub_mod_eq_zero_of_mod_eq h3.symm
      rw [Nat.add_sub_cancel_left] at h5
      exact Nat.dvd_of_mod_eq_zero h5
    have := Nat.le_of_dvd (by omega) h4
    omega
  have hA : GPath.arc₁ z hadj m 0 ∈ GPath.nbPaths c.graph (z 0) m :=
    ⟨GPath.arc₁_zero z hadj m 0, GPath.arc₁_noBack z hadj hnb m 0⟩
  have hB : GPath.arc₂ z hadj m 0 ∈ GPath.nbPaths c.graph (z 0) m :=
    ⟨GPath.arc₂_zero z hadj m hper 0, GPath.arc₂_noBack z hadj hnb m 0⟩
  have gA := F.mem_geods hA
  have gB := F.mem_geods hB
  intro hl
  have := hl _ _ gA.2.2 gB.2.2 (by rw [gA.1, gB.1])
    (by rw [GPath.arc₁_last, GPath.arc₂_last])
  exact GPath.arc_ne z hadj hnb m hper (by omega) 0 this

theorem card_Y_eq_of_small {Y' : Type w} [Group Y'] [Finite Y'] {d : α.Completion Y'}
    (Fd : Facts46 d m) (hsc : c.IsSmall m) (hsd : d.IsSmall m) : Nat.card Y = Nat.card Y' := by
  have hq1 := F.thick1
  have hidx : 0 < α.α1.range.index := by
    unfold RankTwoAmalgam.qOne at hq1
    omega
  have hsph : ∀ k, k ≤ m →
      Nat.card ↥(CosetGeom.sphere k c.xv) = Nat.card ↥(CosetGeom.sphere k d.xv) := by
    intro k hk
    rcases Nat.lt_or_ge k m with hlt | hge
    · rw [F.card_sphere_lt hlt, Fd.card_sphere_lt hlt]
      exact card_nbPaths_eq c d F.faithful Fd.faithful k
    · have hkm : k = m := le_antisymm hk hge
      rw [hkm]
      have e1 := F.card_nbPaths_m (fun a b hab => F.allBij hsc hab)
      have e2 := Fd.card_nbPaths_m (fun a b hab => Fd.allBij hsd hab)
      rw [nbrs_xv_card (c := c) F.faithful] at e1
      rw [nbrs_xv_card (c := d) Fd.faithful] at e2
      have e3 := card_nbPaths_eq c d F.faithful Fd.faithful m
      rw [e1, e2] at e3
      exact Nat.eq_of_mul_eq_mul_right hidx e3
  have hpts : c.ptsCard = d.ptsCard := by
    rw [Facts46.card_pts (c := c) (F.diam_le hsc), Facts46.card_pts (c := d) (Fd.diam_le hsd)]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases he : Even k
    · simp only [he, ite_true]
      exact hsph k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    · simp only [he, ite_false]
  rw [card_Y_eq c F.faithful, card_Y_eq d Fd.faithful, hpts]

end RankTwoAmalgam.Completion

namespace LieSetting

variable {S : LieSetting.{u, w}} {Y : Type w'} [Group Y] [Finite Y]

theorem Facts45L.allBij_iota (hS : S.Facts45L) {a b : S.ι.Γ} (hab : S.ι.graph.dist a b = S.m) :
    BijFirst S.ι S.m a b := by
  have T := hS.transComp
  obtain ⟨P, hP, hPb⟩ := Facts46.exists_geod_path (c := S.ι) (m := S.m) hab
  rcases T.alt hP with ⟨⟨v, hv⟩, -⟩ | ⟨-, hii⟩
  · exact absurd (hS.poly.diam_le a v) (not_le.mpr hv)
  · have := T.geods_bij hii
    rwa [hPb] at this

theorem Facts45L.isSmall_iota (hS : S.Facts45L) : S.ι.IsSmall S.m := by
  obtain ⟨T, hT⟩ := hS.poly.polygon
  exact (hS.facts46 S.ι S.hι).isSmall_of_polygon hT

theorem Facts45L.lemma_F413_2 (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall S.m) : Nat.card Y = Nat.card S.Yb :=
  card_Y_eq_of_small (hS.facts46 β hβ) (hS.facts46 S.ι S.hι) hs hS.isSmall_iota

end LieSetting

end CFSG.Quasithin
