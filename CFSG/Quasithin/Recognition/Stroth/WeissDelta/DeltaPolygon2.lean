module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaPolygon

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

private theorem exists_good_path_of_dist (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {z z' u w : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (huz : c.graph.dist u z = n - 1) (huz' : c.graph.dist u z' = n)
    (hzw : c.graph.Adj z' w) (hwz : w ≠ z) :
    ∃ p : GPath c.graph (2 * n - 1),
      Good (2 * n - 1) p ∧ p 0 = u ∧ p (n - 1) = z ∧ p n = z' ∧ p (n + 1) = w ∧
        c.graph.dist z' (p (2 * n - 1)) = n - 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hxy : c.graph.Adj z z' := adj_base_edge hz
  obtain ⟨g, hg0, hgN, hgnb⟩ := GPath.exists_geodesic' hconn u z huz
  have hggeo : g.IsGeodesic := by
    rw [GPath.IsGeodesic, hg0, hgN]
    exact huz
  have hgn2 : g (n - 2) ≠ z' := by
    intro heq
    have hdist : c.graph.dist u (g (n - 2)) = n - 2 := by
      have := GPath.dist_prefix hconn g hggeo (i := n - 2) (by omega)
      rwa [hg0] at this
    rw [heq] at hdist
    omega
  let q0 : GPath c.graph ((n - 1) + 1) := g.snoc z' (by rw [hgN]; exact hxy)
  have hq0nb : q0.NoBack := by
    refine GPath.noBack_snoc hgnb (by rw [hgN]; exact hxy) ?_
    intro _ h
    rw [show n - 1 - 1 = n - 2 by omega] at h
    exact hgn2 h.symm
  let q1 : GPath c.graph (((n - 1) + 1) + 1) := q0.snoc w (by rw [GPath.snoc_last]; exact hzw)
  have hq1nb : q1.NoBack := by
    refine GPath.noBack_snoc hq0nb (by rw [GPath.snoc_last]; exact hzw) ?_
    intro _
    have hlast : q0 ((n - 1) + 1 - 1) = z := by
      rw [show (n - 1) + 1 - 1 = n - 1 by omega, GPath.snoc_of_le _ _ _ le_rfl, hgN]
    rw [hlast]
    exact hwz
  let q : GPath c.graph (n + 1) :=
    GPath.castLength (by omega : ((n - 1) + 1) + 1 = n + 1) q1
  have hqnb : q.NoBack := GPath.castLength_noBack _ hq1nb
  have hqgood : Good (n + 1) q := hG.short (n + 1) q le_rfl hqnb
  obtain ⟨p, ⟨hpgood, hpeq⟩, -⟩ :=
    hG.existsUnique_extendTo (s := n + 1) (t := 2 * n - 1) q le_rfl (by omega) hqgood
  have hq0_zero : q0 0 = u := by
    rw [show q0 0 = g 0 from GPath.snoc_of_le _ _ _ (by omega), hg0]
  have hq1_zero : q1 0 = u := by
    rw [show q1 0 = q0 0 from GPath.snoc_of_le _ _ _ (by omega), hq0_zero]
  have hp0 : p 0 = u := by
    rw [hpeq 0 (by omega), GPath.castLength_apply, hq1_zero]
  have hq1_nm1 : q1 (n - 1) = z := by
    rw [show q1 (n - 1) = q0 (n - 1) from GPath.snoc_of_le _ _ _ (by omega)]
    rw [show q0 (n - 1) = g (n - 1) from GPath.snoc_of_le _ _ _ le_rfl, hgN]
  have hpnm1 : p (n - 1) = z := by
    rw [hpeq (n - 1) (by omega), GPath.castLength_apply, hq1_nm1]
  have hq0_n : q0 n = z' := by
    have h : q0 ((n - 1) + 1) = z' := GPath.snoc_last g z' _
    simpa [show (n - 1) + 1 = n by omega] using h
  have hq1_n : q1 n = z' := by
    rw [show q1 n = q0 n from GPath.snoc_of_le _ _ _ (by omega), hq0_n]
  have hpn : p n = z' := by
    rw [hpeq n (by omega), GPath.castLength_apply, hq1_n]
  have hpn1 : p (n + 1) = w := by
    rw [hpeq (n + 1) le_rfl, GPath.castLength_apply]
    rw [show n + 1 = ((n - 1) + 1) + 1 by omega]
    exact GPath.snoc_last q0 w _
  have hnb_p : p.NoBack := hG.noBack (2 * n - 1) p hpgood
  have hdrop : (p.drop n (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (2 * n - 1 - n) (by omega) _
      (hnb_p.drop n (by omega))
  have hpost : c.graph.dist z' (p (2 * n - 1)) = n - 1 := by
    rw [GPath.IsGeodesic, GPath.drop_apply _ _ _ (Nat.zero_le _),
      GPath.drop_apply _ _ _ (le_rfl (a := 2 * n - 1 - n))] at hdrop
    rw [show n + 0 = n by omega] at hdrop
    rw [hpn] at hdrop
    rw [show n + (2 * n - 1 - n) = 2 * n - 1 by omega] at hdrop
    rw [show 2 * n - 1 - n = n - 1 by omega] at hdrop
    exact hdrop
  exact ⟨p, hpgood, hp0, hpnm1, hpn, hpn1, hpost⟩

private theorem isGeodesic_castLength {V : Type} {Γ : SimpleGraph V} {m k : ℕ} (h : m = k)
    {p : GPath Γ m} (hp : p.IsGeodesic) : (GPath.castLength h p).IsGeodesic := by
  show Γ.dist ((GPath.castLength h p) 0) ((GPath.castLength h p) k) = k
  rw [GPath.castLength_apply, GPath.castLength_apply, ← h]
  exact hp

private theorem exists_periodic_polygon (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    ∃ z : ℕ → ↥(edgeBall (n - 1) c),
      (∀ i, (delta c Good n).Adj (z i) (z (i + 1))) ∧
      (∀ i, z i ≠ z (i + 2)) ∧
      (∀ i, z (i + 2 * n) = z i) ∧
      (delta c Good n).dist (z 0) (z n) = n := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  obtain ⟨s, hsnb, hsx, hsne⟩ := exists_backward_noBack (Γ := c.graph) hdeg
    (adj_base_edge (Or.inl ⟨rfl, rfl⟩)) (n - 1)
  have hsgeo : s.IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) s hsnb
  have hs0x : c.graph.dist (s 0) c.xv = n - 1 := by
    have h := hsgeo
    rw [GPath.IsGeodesic, hsx] at h
    exact h
  have hsy_adj : c.graph.Adj (s (n - 1)) c.lv := by
    rw [hsx]
    exact adj_base_edge (Or.inl ⟨rfl, rfl⟩)
  have hsy_nb : (s.snoc c.lv hsy_adj).NoBack := by
    refine GPath.noBack_snoc hsnb hsy_adj ?_
    intro _
    have h := hsne (by omega : 0 < n - 1)
    intro heq
    refine h ?_
    rw [show n - 1 - 1 = n - 2 by omega] at heq
    exact heq.symm
  have hsy_geo : (s.snoc c.lv hsy_adj).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU ((n - 1) + 1) (by omega) _ hsy_nb
  have hsy : c.graph.dist (s 0) c.lv = n := by
    have h := hsy_geo
    rw [GPath.IsGeodesic, GPath.snoc_of_le _ _ _ (Nat.zero_le _),
      GPath.snoc_last] at h
    rw [show (n - 1) + 1 = n by omega] at h
    exact h
  obtain ⟨w2, hyw2, hw2x⟩ := hdeg c.lv c.xv CosetGeom.adj_γ₀_γ₁.symm
  obtain ⟨p, hpgood, hp0, hpnm1, hpn, hpn1, hpost⟩ :=
    exists_good_path_of_dist hn hgirth hG (z := c.xv) (z' := c.lv) (u := s 0) (w := w2)
      (Or.inl ⟨rfl, rfl⟩) hs0x hsy hyw2 hw2x
  have hnb_p : p.NoBack := hG.noBack (2 * n - 1) p hpgood
  have hpre_geo : (p.take (n - 1) (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) _
      (hnb_p.take (n - 1) (by omega))
  have hpre_dist : c.graph.dist (p 0) (p (n - 1)) = n - 1 := by
    have h := hpre_geo
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
      GPath.take_apply_of_le _ _ _ le_rfl] at h
    exact h
  have hpost_geo : (p.drop n (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (2 * n - 1 - n) (by omega) _
      (hnb_p.drop n (by omega))
  have hdist_early : ∀ j, j ≤ n - 1 → c.graph.dist (p j) c.xv = n - 1 - j := by
    intro j hj
    have hdj : c.graph.dist (p 0) (p j) = j := by
      have h := GPath.dist_prefix hconn (p.take (n - 1) (by omega)) hpre_geo (i := j) hj
      rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
        GPath.take_apply_of_le _ _ _ hj] at h
      exact h
    have hsub : c.graph.dist (p j) (p (n - 1)) ≤ n - 1 - j := by
      have h := GPath.dist_le_sub hconn (p.take (n - 1) (by omega)) (i := j) (j := n - 1)
        hj le_rfl
      rw [GPath.take_apply_of_le _ _ _ hj,
        GPath.take_apply_of_le _ _ _ le_rfl] at h
      exact h
    have htri := hconn.dist_triangle (u := p 0) (v := p j) (w := p (n - 1))
    rw [hdj, hpre_dist, hpnm1] at htri
    rw [hpnm1] at hsub
    omega
  have hdist_late : ∀ j, n ≤ j → j ≤ 2 * n - 1 → c.graph.dist (p j) c.lv = j - n := by
    intro j hj hj'
    have hdj : c.graph.dist (p n) (p j) = j - n := by
      have h := GPath.dist_prefix hconn (p.drop n (by omega)) hpost_geo (i := j - n)
        (by omega)
      rw [GPath.drop_apply _ _ _ (Nat.zero_le _),
        GPath.drop_apply _ _ _ (by omega),
        show n + (j - n) = j by omega] at h
      exact h
    rw [hpn] at hdj
    rwa [SimpleGraph.dist_comm]
  have hp0height : height c (p 0) = n - 1 := by
    rw [height, hp0, hs0x, hsy]
    omega
  have hheight_last : height c (p (2 * n - 2)) ≤ n - 2 := by
    have hle : height c (p (2 * n - 2)) ≤ c.graph.dist (p (2 * n - 2)) c.lv :=
      min_le_right _ _
    have hd := hdist_late (2 * n - 2) (by omega) (by omega)
    rw [hd] at hle
    omega
  have hmem_pre : ∀ j, j ≤ n - 1 → p j ∈ edgeBall (n - 1) c := by
    intro j hj
    exact Or.inl (by rw [SimpleGraph.dist_comm]; rw [hdist_early j hj]; omega)
  have hmem_post : ∀ j, n ≤ j → j ≤ 2 * n - 1 → p j ∈ edgeBall (n - 1) c := by
    intro j hj hj'
    exact Or.inr (by rw [SimpleGraph.dist_comm, hdist_late j hj hj']; omega)
  have hmem : ∀ j, j ≤ 2 * n - 1 → p j ∈ edgeBall (n - 1) c := by
    intro j hj
    by_cases hle : j ≤ n - 1
    · exact hmem_pre j hle
    · exact hmem_post j (by omega) hj
  have hmod_le : ∀ i, i % (2 * n) ≤ 2 * n - 1 := by
    intro i
    have := Nat.mod_lt i (by omega : 0 < 2 * n)
    omega
  let z : ℕ → ↥(edgeBall (n - 1) c) := fun i =>
    ⟨p (i % (2 * n)), hmem _ (hmod_le i)⟩
  have hz_apply : ∀ i, (z i : c.Γ) = p (i % (2 * n)) := fun _ => rfl
  have hmod_lt : ∀ i, i % (2 * n) < 2 * n := fun i => Nat.mod_lt _ (by omega)
  have hmod_succ : ∀ i, (i + 1) % (2 * n) = (i % (2 * n) + 1) % (2 * n) := by
    intro i
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2 * n)]
  have hmod_add_lt : ∀ m, m < 2 * n - 1 → (m + 1) % (2 * n) = m + 1 := by
    intro m hm
    rw [Nat.mod_eq_of_lt]
    omega
  have hmod_add_two : ∀ m, m < 2 * n - 1 → (m + 2) % (2 * n) =
      if m = 2 * n - 2 then 0 else m + 2 := by
    intro m hm
    by_cases hlast : m = 2 * n - 2
    · subst hlast
      rw [if_pos rfl]
      have h : 2 * n - 2 + 2 = 2 * n := by omega
      rw [h, Nat.mod_self]
    · rw [if_neg hlast, Nat.mod_eq_of_lt]
      omega
  have hper : ∀ i, z (i + 2 * n) = z i := by
    intro i
    apply Subtype.ext
    rw [hz_apply, hz_apply, Nat.add_mod_right]
  have hadj : ∀ i, (delta c Good n).Adj (z i) (z (i + 1)) := by
    intro i
    set m := i % (2 * n) with hm
    have hm_lt : m < 2 * n := by rw [hm]; exact hmod_lt i
    have hzi : (z i : c.Γ) = p m := by rw [hz_apply, ← hm]
    have hzi1 : (z (i + 1) : c.Γ) = p ((m + 1) % (2 * n)) := by
      rw [hz_apply, hmod_succ, ← hm]
    by_cases hlast : m = 2 * n - 1
    · have hnext : (m + 1) % (2 * n) = 0 := by
        rw [hlast]
        have h : 2 * n - 1 + 1 = 2 * n := by omega
        rw [h, Nat.mod_self]
      have hzi1' : (z (i + 1) : c.Γ) = p 0 := by rw [hzi1, hnext]
      have hzi' : (z i : c.Γ) = p (2 * n - 1) := by rw [hzi, hlast]
      have hB : TypeB c Good n ((z (i + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)
          ((z i : ↥(edgeBall (n - 1) c)) : c.Γ) := by
        rw [hzi1', hzi']
        exact ⟨p, hpgood, rfl, rfl, Or.inl ⟨hpnm1, hpn⟩⟩
      exact (delta_adj_of_typeB hn hgirth hG hB).symm
    · have hmlt : m < 2 * n - 1 := by omega
      have hnext : (m + 1) % (2 * n) = m + 1 := hmod_add_lt m hmlt
      have hzi1' : (z (i + 1) : c.Γ) = p (m + 1) := by rw [hzi1, hnext]
      by_cases hearly : m ≤ n - 2
      · have hheight : height c ((z (i + 1) : ↥(edgeBall (n - 1) c)) : c.Γ) ≤ n - 2 := by
          rw [hzi1']
          have hle : height c (p (m + 1)) ≤ c.graph.dist (p (m + 1)) c.xv :=
            min_le_left _ _
          rw [hdist_early (m + 1) (by omega)] at hle
          omega
        have hgamma : c.graph.Adj ((z (i + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)
            ((z i : ↥(edgeBall (n - 1) c)) : c.Γ) := by
          rw [hzi1', hzi]
          exact (p.adj m (by omega)).symm
        exact ((delta_adj_iff_of_height_le hn hgirth hG (u := z (i + 1)) hheight).mpr
          hgamma).symm
      · have hheight : height c ((z i : ↥(edgeBall (n - 1) c)) : c.Γ) ≤ n - 2 := by
          rw [hzi]
          by_cases hx : m = n - 1
          · rw [hx]
            have h0 : c.graph.dist (p (n - 1)) c.xv = 0 := by
              rw [hdist_early (n - 1) le_rfl]
              omega
            calc height c (p (n - 1)) ≤ c.graph.dist (p (n - 1)) c.xv := min_le_left _ _
              _ = 0 := h0
              _ ≤ n - 2 := by omega
          · have hmn : n ≤ m := by omega
            have hle : height c (p m) ≤ c.graph.dist (p m) c.lv := min_le_right _ _
            rw [hdist_late m hmn (by omega)] at hle
            omega
        have hgamma : c.graph.Adj ((z i : ↥(edgeBall (n - 1) c)) : c.Γ)
            ((z (i + 1) : ↥(edgeBall (n - 1) c)) : c.Γ) := by
          rw [hzi, hzi1']
          exact p.adj m (by omega)
        exact (delta_adj_iff_of_height_le hn hgirth hG (u := z i) hheight).mpr hgamma
  have hnb : ∀ i, z i ≠ z (i + 2) := by
    intro i hEq
    set m := i % (2 * n) with hm
    have hval : p m = p ((i + 2) % (2 * n)) := by
      have h := congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hEq
      rw [hz_apply, hz_apply, ← hm] at h
      exact h
    have hm_lt : m < 2 * n := by rw [hm]; exact hmod_lt i
    have hmod2 : (i + 2) % (2 * n) = (m + 2) % (2 * n) := by
      rw [Nat.add_mod, ← hm, Nat.mod_eq_of_lt (by omega : 2 < 2 * n)]
    by_cases hlast : m = 2 * n - 1
    · have h2 : (i + 2) % (2 * n) = 1 := by
        rw [hmod2, hlast]
        have h : 2 * n - 1 + 2 = 1 + 2 * n := by omega
        rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < 2 * n)]
      rw [hlast] at hval
      rw [h2] at hval
      have hA0 : (p.drop n (by omega)).IsGeodesic := hpost_geo
      let A : GPath c.graph (n - 1) :=
        GPath.castLength (by omega : 2 * n - 1 - n = n - 1) (p.drop n (by omega))
      have hAgeo : A.IsGeodesic := isGeodesic_castLength _ hA0
      have hA0v : A 0 = p n := by
        show (p.drop n (by omega)).toFun 0 = p n
        exact (GPath.drop_apply (p := p) n (by omega) (i := 0) (by omega)).trans
          (by rw [Nat.add_zero])
      have hAend : A (n - 1) = p (2 * n - 1) := by
        show (GPath.castLength _ (p.drop n (by omega))) (n - 1) = p (2 * n - 1)
        rw [GPath.castLength_apply]
        rw [show n - 1 = 2 * n - 1 - n by omega]
        rw [GPath.drop_apply _ _ _ le_rfl]
        congr 1
        omega
      let B : GPath c.graph (n - 1) := (p.drop 1 (by omega)).take (n - 1) (by omega)
      have hBnb : B.NoBack := (hnb_p.drop 1 (by omega)).take (n - 1) (by omega)
      have hBgeo : B.IsGeodesic :=
        GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) B hBnb
      have hBrev_geo : B.rev.IsGeodesic := hBgeo.rev
      have hB0 : B 0 = p 1 := by
        show (p.drop 1 (by omega)).take (n - 1) (by omega) 0 = p 1
        rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]
        exact (GPath.drop_apply (p := p) 1 (by omega) (i := 0) (by omega)).trans
          (by rw [Nat.add_zero])
      have hBend : B (n - 1) = p n := by
        show (p.drop 1 (by omega)).take (n - 1) (by omega) (n - 1) = p n
        rw [GPath.take_apply_of_le _ _ _ le_rfl]
        rw [GPath.drop_apply _ _ _ (by omega)]
        congr 1
        omega
      have hBrev0 : B.rev 0 = p n := by
        rw [GPath.rev_apply _ (by omega), Nat.sub_zero, hBend]
      have hBrevend : B.rev (n - 1) = p 1 := by
        rw [GPath.rev_apply _ le_rfl, Nat.sub_self, hB0]
      have hstart : A 0 = B.rev 0 := by rw [hA0v, hBrev0]
      have hend : A (n - 1) = B.rev (n - 1) := by rw [hAend, hBrevend, hval]
      have heq : A = B.rev :=
        hU (n - 1) A B.rev hAgeo hBrev_geo hstart hend (by omega)
      have h1 : A 1 = B.rev 1 := congrArg (fun r : GPath c.graph (n - 1) => r 1) heq
      have hA1 : A 1 = p (n + 1) := by
        show (GPath.castLength _ (p.drop n (by omega))) 1 = p (n + 1)
        rw [GPath.castLength_apply, GPath.drop_apply _ _ _ (by omega)]
      have hBrev1 : B.rev 1 = p (n - 1) := by
        rw [GPath.rev_apply _ (by omega)]
        rw [show n - 1 - 1 = n - 2 by omega]
        show (p.drop 1 (by omega)).take (n - 1) (by omega) (n - 2) = p (n - 1)
        rw [GPath.take_apply_of_le _ _ _ (by omega)]
        rw [GPath.drop_apply _ _ _ (by omega)]
        congr 1
        omega
      rw [hA1, hBrev1] at h1
      have h1' : p (n - 1) = p (n - 1 + 2) := by
        rw [show n - 1 + 2 = n + 1 by omega]
        exact h1.symm
      exact (hnb_p (n - 1) (by omega)) h1'
    · have hmlt : m < 2 * n - 1 := by omega
      have h2 : (i + 2) % (2 * n) = if m = 2 * n - 2 then 0 else m + 2 := by
        rw [hmod2]
        exact hmod_add_two m hmlt
      by_cases hpen : m = 2 * n - 2
      · rw [if_pos hpen] at h2
        rw [h2] at hval
        have hle : height c (p 0) ≤ n - 2 := by
          rw [← hval, hpen]
          exact hheight_last
        omega
      · rw [if_neg hpen] at h2
        rw [h2] at hval
        exact (hnb_p m (by omega)) hval
  have hdiam : (delta c Good n).dist (z 0) (z n) = n := by
    have hUδ : UniqueGeod (delta c Good n) n :=
      uniqueGeod_of_le_egirth (delta_connected hn hgirth hG)
        (le_egirth_delta hn hgirth hG hdeg)
    obtain ⟨col, hcol⟩ := delta_bipartite hn hgirth hG
    have hseqnb : (GPath.seqPath z hadj 0 n).NoBack := by
      intro j hj
      rw [GPath.seqPath_apply z hadj 0 n (by omega),
        GPath.seqPath_apply z hadj 0 n (by omega)]
      have h := hnb j
      simpa only [Nat.zero_add] using h
    have hgeo := GPath.isGeodesic_of_noBack (delta_connected hn hgirth hG) hcol hUδ n le_rfl
      (GPath.seqPath z hadj 0 n) hseqnb
    rw [GPath.IsGeodesic] at hgeo
    rw [GPath.seqPath_apply z hadj 0 n (Nat.zero_le _),
      GPath.seqPath_apply z hadj 0 n le_rfl, Nat.zero_add, Nat.zero_add] at hgeo
    exact hgeo
  exact ⟨z, hadj, hnb, hper, hdiam⟩

private theorem eq_succ_of_eq_end (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {u z' w1 w2 : c.Γ}
    {p q : GPath c.graph (2 * n - 1)} (hp : Good (2 * n - 1) p) (hq : Good (2 * n - 1) q)
    (hp0 : p 0 = u) (hq0 : q 0 = u) (hpn : p n = z') (hqn : q n = z')
    (hpw : p (n + 1) = w1) (hqw : q (n + 1) = w2)
    (hend : p (2 * n - 1) = q (2 * n - 1)) : w1 = w2 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hpnb : p.NoBack := hG.noBack (2 * n - 1) p hp
  have hqnb : q.NoBack := hG.noBack (2 * n - 1) q hq
  have hdrop_p : (p.drop n (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (2 * n - 1 - n) (by omega) _
      (hpnb.drop n (by omega))
  have hdrop_q : (q.drop n (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (2 * n - 1 - n) (by omega) _
      (hqnb.drop n (by omega))
  let A : GPath c.graph (n - 1) :=
    GPath.castLength (by omega : 2 * n - 1 - n = n - 1) (p.drop n (by omega))
  let B : GPath c.graph (n - 1) :=
    GPath.castLength (by omega : 2 * n - 1 - n = n - 1) (q.drop n (by omega))
  have hAgeo : A.IsGeodesic := isGeodesic_castLength _ hdrop_p
  have hBgeo : B.IsGeodesic := isGeodesic_castLength _ hdrop_q
  have hA0 : A 0 = z' := by
    show (p.drop n (by omega)).toFun 0 = z'
    exact (GPath.drop_apply (p := p) n (by omega) (i := 0) (by omega)).trans
      (by rw [Nat.add_zero]; exact hpn)
  have hB0 : B 0 = z' := by
    show (q.drop n (by omega)).toFun 0 = z'
    exact (GPath.drop_apply (p := q) n (by omega) (i := 0) (by omega)).trans
      (by rw [Nat.add_zero]; exact hqn)
  have hAend : A (n - 1) = p (2 * n - 1) := by
    show (p.drop n (by omega)).toFun (n - 1) = p (2 * n - 1)
    exact (GPath.drop_apply (p := p) n (by omega) (i := n - 1) (by omega)).trans
      (by congr 1; omega)
  have hBend : B (n - 1) = q (2 * n - 1) := by
    show (q.drop n (by omega)).toFun (n - 1) = q (2 * n - 1)
    exact (GPath.drop_apply (p := q) n (by omega) (i := n - 1) (by omega)).trans
      (by congr 1; omega)
  have hAB : A = B :=
    hU (n - 1) A B hAgeo hBgeo (by rw [hA0, hB0])
      (by rw [hAend, hBend]; exact hend) (by omega)
  have h1 : A 1 = B 1 := congrArg (fun r : GPath c.graph (n - 1) => r 1) hAB
  have hA1 : A 1 = w1 := by
    show (p.drop n (by omega)).toFun 1 = w1
    exact (GPath.drop_apply (p := p) n (by omega) (i := 1) (by omega)).trans
      (by rw [show n + 1 = n + 1 from rfl]; exact hpw)
  have hB1 : B 1 = w2 := by
    show (q.drop n (by omega)).toFun 1 = w2
    exact (GPath.drop_apply (p := q) n (by omega) (i := 1) (by omega)).trans
      (by rw [show n + 1 = n + 1 from rfl]; exact hqw)
  rw [hA1, hB1] at h1
  exact h1

private theorem exists_two_delta_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (u : ↥(edgeBall (n - 1) c)) :
    ∃ v w, (delta c Good n).Adj u v ∧ (delta c Good n).Adj u w ∧ v ≠ w := by
  have hxy : c.graph.Adj c.xv c.lv := adj_base_edge (Or.inl ⟨rfl, rfl⟩)
  by_cases hux : (u : c.Γ) = c.xv
  · obtain ⟨w, hxw, hwy⟩ := hdeg c.xv c.lv hxy
    have hwmem : w ∈ edgeBall (n - 1) c :=
      mem_edgeBall_of_adj_of_height_le (c := c) (n := n) (by omega) (by rw [height_xv]; omega) hxw
    have hwadj : (delta c Good n).Adj u ⟨w, hwmem⟩ := by
      have hu : u = deltaXv c n := Subtype.ext hux
      rw [hu]
      refine (delta_adj_iff_of_height_le hn hgirth hG (u := deltaXv c n) ?_).mpr hxw
      change height c c.xv ≤ n - 2
      rw [height_xv]
      omega
    refine ⟨deltaLv c n, ⟨w, hwmem⟩, ?_, hwadj, ?_⟩
    · have hu : u = deltaXv c n := Subtype.ext hux
      rw [hu]
      exact delta_adj_deltaXv_deltaLv hn
    · intro hEq
      exact hwy (by simpa [deltaLv] using (congrArg Subtype.val hEq).symm)
  by_cases hul : (u : c.Γ) = c.lv
  · obtain ⟨w, hyw, hwx⟩ := hdeg c.lv c.xv hxy.symm
    have hwmem : w ∈ edgeBall (n - 1) c :=
      mem_edgeBall_of_adj_of_height_le (c := c) (n := n) (by omega) (by rw [height_lv]; omega) hyw
    have hwadj : (delta c Good n).Adj u ⟨w, hwmem⟩ := by
      have hu : u = deltaLv c n := Subtype.ext hul
      rw [hu]
      refine (delta_adj_iff_of_height_le hn hgirth hG (u := deltaLv c n) ?_).mpr hyw
      change height c c.lv ≤ n - 2
      rw [height_lv]
      omega
    refine ⟨deltaXv c n, ⟨w, hwmem⟩, ?_, hwadj, ?_⟩
    · have hu : u = deltaLv c n := Subtype.ext hul
      rw [hu]
      exact (delta_adj_deltaXv_deltaLv hn).symm
    · intro hEq
      exact hwx (by simpa [deltaXv] using (congrArg Subtype.val hEq).symm)
  obtain ⟨w0, ⟨huw0, hw0h⟩, -⟩ := existsUnique_adj_height_pred hgirth u.2 hux hul
  have hule : height c (u : c.Γ) ≤ n - 1 := height_le_of_mem_edgeBall u.2
  have hw0le : height c w0 ≤ n - 2 := by omega
  have hw0mem : w0 ∈ edgeBall (n - 1) c := mem_edgeBall_of_height_le (by omega)
  let w0' : ↥(edgeBall (n - 1) c) := ⟨w0, hw0mem⟩
  have hw0adj : (delta c Good n).Adj u w0' :=
    ((delta_adj_iff_of_height_le hn hgirth hG (u := w0') hw0le).mpr huw0.symm).symm
  by_cases htop : height c (u : c.Γ) ≤ n - 2
  · obtain ⟨w, huw, hwne⟩ := hdeg (u : c.Γ) w0 huw0
    have hwmem : w ∈ edgeBall (n - 1) c :=
      mem_edgeBall_of_adj_of_height_le (c := c) (n := n) (by omega) htop huw
    let w' : ↥(edgeBall (n - 1) c) := ⟨w, hwmem⟩
    have hwadj : (delta c Good n).Adj u w' :=
      (delta_adj_iff_of_height_le hn hgirth hG (u := u) htop).mpr huw
    refine ⟨w0', w', hw0adj, hwadj, ?_⟩
    intro hEq
    exact hwne (congrArg Subtype.val hEq).symm
  · have hheight : height c (u : c.Γ) = n - 1 := by omega
    have hmin : min (c.graph.dist (u : c.Γ) c.xv) (c.graph.dist (u : c.Γ) c.lv) = n - 1 := by
      simpa [height] using hheight
    have hpar := dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) (w := (u : c.Γ))
    have key : ∃ e : ↥(edgeBall (n - 1) c),
        TypeB c Good n (u : c.Γ) (e : c.Γ) ∧ e ≠ w0' := by
      rcases hpar with hpar | hpar
      · have huxn : c.graph.dist c.xv (u : c.Γ) = n := by
          rw [SimpleGraph.dist_comm]
          rw [min_eq_right (by omega)] at hmin
          omega
        obtain ⟨e, heB, hedist⟩ := exists_typeB_of_far hn hgirth hG hdeg
          (Or.inl ⟨rfl, rfl⟩) u.2 (by omega)
        have hemem : e ∈ edgeBall (n - 1) c := Or.inl (le_of_eq hedist)
        refine ⟨⟨e, hemem⟩, ?_, ?_⟩
        · exact heB
        · intro hEq
          have hheighte : height c (e : c.Γ) = n - 1 :=
            (height_eq_of_typeB c hn hgirth hG heB).2
          have hh : height c (e : c.Γ) = height c w0 :=
            congrArg (fun z : ↥(edgeBall (n - 1) c) => height c (z : c.Γ)) hEq
          omega
      · have huyn : c.graph.dist c.lv (u : c.Γ) = n := by
          rw [SimpleGraph.dist_comm]
          rw [min_eq_left (by omega)] at hmin
          omega
        obtain ⟨e, heB, hedist⟩ := exists_typeB_of_far hn hgirth hG hdeg
          (Or.inr ⟨rfl, rfl⟩) u.2 (by omega)
        have hemem : e ∈ edgeBall (n - 1) c := Or.inr (le_of_eq hedist)
        refine ⟨⟨e, hemem⟩, ?_, ?_⟩
        · exact heB
        · intro hEq
          have hheighte : height c (e : c.Γ) = n - 1 :=
            (height_eq_of_typeB c hn hgirth hG heB).2
          have hh : height c (e : c.Γ) = height c w0 :=
            congrArg (fun z : ↥(edgeBall (n - 1) c) => height c (z : c.Γ)) hEq
          omega
    obtain ⟨e, heB, hene⟩ := key
    exact ⟨w0', e, hw0adj, delta_adj_of_typeB hn hgirth hG heB, hene.symm⟩

private theorem exists_three_delta_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (h3 : ∀ v w w' : c.Γ, c.graph.Adj v w → c.graph.Adj v w' →
      ∃ u, c.graph.Adj v u ∧ u ≠ w ∧ u ≠ w') (u : ↥(edgeBall (n - 1) c)) :
    ∃ a b d, (delta c Good n).Adj u a ∧ (delta c Good n).Adj u b ∧
      (delta c Good n).Adj u d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d := by
  have hxy : c.graph.Adj c.xv c.lv := adj_base_edge (Or.inl ⟨rfl, rfl⟩)
  have hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ x, c.graph.Adj v x ∧ x ≠ w := by
    intro v w hvw
    obtain ⟨x, hx, h1, -⟩ := h3 v w w hvw hvw
    exact ⟨x, hx, h1⟩
  by_cases htop : height c (u : c.Γ) ≤ n - 2
  · obtain ⟨w0, huw0, hw0mem⟩ : ∃ w0 : c.Γ, c.graph.Adj (u : c.Γ) w0 ∧
        w0 ∈ edgeBall (n - 1) c := by
      by_cases hux : (u : c.Γ) = c.xv
      · exact ⟨c.lv, hux ▸ hxy, Or.inr (by simp)⟩
      by_cases hul : (u : c.Γ) = c.lv
      · exact ⟨c.xv, hul ▸ hxy.symm, Or.inl (by simp)⟩
      obtain ⟨w, ⟨huw, -⟩, -⟩ := existsUnique_adj_height_pred hgirth u.2 hux hul
      exact ⟨w, huw, mem_edgeBall_of_adj_of_height_le (c := c) (n := n) (by omega) htop huw⟩
    obtain ⟨w1, huw1, hw1ne0, -⟩ := h3 (u : c.Γ) w0 w0 huw0 huw0
    obtain ⟨w2, huw2, hw2ne0, hw2ne1⟩ := h3 (u : c.Γ) w0 w1 huw0 huw1
    have hw1mem : w1 ∈ edgeBall (n - 1) c :=
      mem_edgeBall_of_adj_of_height_le (c := c) (n := n) (by omega) htop huw1
    have hw2mem : w2 ∈ edgeBall (n - 1) c :=
      mem_edgeBall_of_adj_of_height_le (c := c) (n := n) (by omega) htop huw2
    let w0' : ↥(edgeBall (n - 1) c) := ⟨w0, hw0mem⟩
    let w1' : ↥(edgeBall (n - 1) c) := ⟨w1, hw1mem⟩
    let w2' : ↥(edgeBall (n - 1) c) := ⟨w2, hw2mem⟩
    have hd0 : (delta c Good n).Adj u w0' :=
      (delta_adj_iff_of_height_le hn hgirth hG (u := u) htop).mpr huw0
    have hd1 : (delta c Good n).Adj u w1' :=
      (delta_adj_iff_of_height_le hn hgirth hG (u := u) htop).mpr huw1
    have hd2 : (delta c Good n).Adj u w2' :=
      (delta_adj_iff_of_height_le hn hgirth hG (u := u) htop).mpr huw2
    refine ⟨w0', w1', w2', hd0, hd1, hd2, ?_, ?_, ?_⟩
    · intro h
      exact hw1ne0 (congrArg Subtype.val h).symm
    · intro h
      exact hw2ne0 (congrArg Subtype.val h).symm
    · intro h
      exact hw2ne1 (congrArg Subtype.val h).symm
  · have hheight : height c (u : c.Γ) = n - 1 := by
      have := height_le_of_mem_edgeBall u.2
      omega
    have hux : (u : c.Γ) ≠ c.xv := by
      intro h
      rw [h, height_xv] at hheight
      omega
    have hul : (u : c.Γ) ≠ c.lv := by
      intro h
      rw [h, height_lv] at hheight
      omega
    obtain ⟨w0, ⟨huw0, hw0h⟩, -⟩ := existsUnique_adj_height_pred hgirth u.2 hux hul
    have hw0le : height c w0 ≤ n - 2 := by omega
    have hw0mem : w0 ∈ edgeBall (n - 1) c := mem_edgeBall_of_height_le (by omega)
    let w0' : ↥(edgeBall (n - 1) c) := ⟨w0, hw0mem⟩
    have hw0adj : (delta c Good n).Adj u w0' :=
      ((delta_adj_iff_of_height_le hn hgirth hG (u := w0') hw0le).mpr huw0.symm).symm
    have hmin : min (c.graph.dist (u : c.Γ) c.xv) (c.graph.dist (u : c.Γ) c.lv) = n - 1 := by
      simpa [height] using hheight
    have hpar := dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) (w := (u : c.Γ))
    have key : ∃ e1 e2 : ↥(edgeBall (n - 1) c),
        TypeB c Good n (u : c.Γ) (e1 : c.Γ) ∧ TypeB c Good n (u : c.Γ) (e2 : c.Γ) ∧
        e1 ≠ e2 ∧ e1 ≠ w0' ∧ e2 ≠ w0' := by
      rcases hpar with hpar | hpar
      · have huy : c.graph.dist (u : c.Γ) c.lv = n - 1 := by
          rw [min_eq_right (by omega)] at hmin
          exact hmin
        have huxn : c.graph.dist (u : c.Γ) c.xv = n := by omega
        obtain ⟨w1, hxw1, hw1y, -⟩ := h3 c.xv c.lv c.lv hxy hxy
        obtain ⟨w2, hxw2, hw2y, hw2w1⟩ := h3 c.xv c.lv w1 hxy hxw1
        obtain ⟨p1, hp1, hp1_0, hp1_nm1, hp1_n, hp1_n1, hp1_post⟩ :=
          exists_good_path_of_dist hn hgirth hG (z := c.lv) (z' := c.xv) (u := (u : c.Γ))
            (w := w1) (Or.inr ⟨rfl, rfl⟩) huy huxn hxw1 hw1y
        obtain ⟨p2, hp2, hp2_0, hp2_nm1, hp2_n, hp2_n1, hp2_post⟩ :=
          exists_good_path_of_dist hn hgirth hG (z := c.lv) (z' := c.xv) (u := (u : c.Γ))
            (w := w2) (Or.inr ⟨rfl, rfl⟩) huy huxn hxw2 hw2y
        have hpmem1 : p1 (2 * n - 1) ∈ edgeBall (n - 1) c := Or.inl (le_of_eq hp1_post)
        have hpmem2 : p2 (2 * n - 1) ∈ edgeBall (n - 1) c := Or.inl (le_of_eq hp2_post)
        let e1 : ↥(edgeBall (n - 1) c) := ⟨p1 (2 * n - 1), hpmem1⟩
        let e2 : ↥(edgeBall (n - 1) c) := ⟨p2 (2 * n - 1), hpmem2⟩
        have hTB1 : TypeB c Good n (u : c.Γ) (e1 : c.Γ) :=
          ⟨p1, hp1, hp1_0, rfl, Or.inr ⟨hp1_nm1, hp1_n⟩⟩
        have hTB2 : TypeB c Good n (u : c.Γ) (e2 : c.Γ) :=
          ⟨p2, hp2, hp2_0, rfl, Or.inr ⟨hp2_nm1, hp2_n⟩⟩
        have he12 : e1 ≠ e2 := by
          intro he
          have hweq : w1 = w2 :=
            eq_succ_of_eq_end hn hgirth hG hp1 hp2 hp1_0 hp2_0 hp1_n hp2_n hp1_n1 hp2_n1
              (by exact congrArg Subtype.val he)
          exact hw2w1 hweq.symm
        have he1 : e1 ≠ w0' := by
          intro he
          have hheighte : height c (e1 : c.Γ) = n - 1 :=
            (height_eq_of_typeB c hn hgirth hG hTB1).2
          have hh : height c (e1 : c.Γ) = height c w0 :=
            congrArg (fun z : ↥(edgeBall (n - 1) c) => height c (z : c.Γ)) he
          omega
        have he2 : e2 ≠ w0' := by
          intro he
          have hheighte : height c (e2 : c.Γ) = n - 1 :=
            (height_eq_of_typeB c hn hgirth hG hTB2).2
          have hh : height c (e2 : c.Γ) = height c w0 :=
            congrArg (fun z : ↥(edgeBall (n - 1) c) => height c (z : c.Γ)) he
          omega
        exact ⟨e1, e2, hTB1, hTB2, he12, he1, he2⟩
      · have huxn : c.graph.dist (u : c.Γ) c.xv = n - 1 := by
          rw [min_eq_left (by omega)] at hmin
          exact hmin
        have huyn : c.graph.dist (u : c.Γ) c.lv = n := by omega
        obtain ⟨w1, hyw1, hw1x, -⟩ := h3 c.lv c.xv c.xv hxy.symm hxy.symm
        obtain ⟨w2, hyw2, hw2x, hw2w1⟩ := h3 c.lv c.xv w1 hxy.symm hyw1
        obtain ⟨p1, hp1, hp1_0, hp1_nm1, hp1_n, hp1_n1, hp1_post⟩ :=
          exists_good_path_of_dist hn hgirth hG (z := c.xv) (z' := c.lv) (u := (u : c.Γ))
            (w := w1) (Or.inl ⟨rfl, rfl⟩) huxn huyn hyw1 hw1x
        obtain ⟨p2, hp2, hp2_0, hp2_nm1, hp2_n, hp2_n1, hp2_post⟩ :=
          exists_good_path_of_dist hn hgirth hG (z := c.xv) (z' := c.lv) (u := (u : c.Γ))
            (w := w2) (Or.inl ⟨rfl, rfl⟩) huxn huyn hyw2 hw2x
        have hpmem1 : p1 (2 * n - 1) ∈ edgeBall (n - 1) c := Or.inr (le_of_eq hp1_post)
        have hpmem2 : p2 (2 * n - 1) ∈ edgeBall (n - 1) c := Or.inr (le_of_eq hp2_post)
        let e1 : ↥(edgeBall (n - 1) c) := ⟨p1 (2 * n - 1), hpmem1⟩
        let e2 : ↥(edgeBall (n - 1) c) := ⟨p2 (2 * n - 1), hpmem2⟩
        have hTB1 : TypeB c Good n (u : c.Γ) (e1 : c.Γ) :=
          ⟨p1, hp1, hp1_0, rfl, Or.inl ⟨hp1_nm1, hp1_n⟩⟩
        have hTB2 : TypeB c Good n (u : c.Γ) (e2 : c.Γ) :=
          ⟨p2, hp2, hp2_0, rfl, Or.inl ⟨hp2_nm1, hp2_n⟩⟩
        have he12 : e1 ≠ e2 := by
          intro he
          have hweq : w1 = w2 :=
            eq_succ_of_eq_end hn hgirth hG hp1 hp2 hp1_0 hp2_0 hp1_n hp2_n hp1_n1 hp2_n1
              (by exact congrArg Subtype.val he)
          exact hw2w1 hweq.symm
        have he1 : e1 ≠ w0' := by
          intro he
          have hheighte : height c (e1 : c.Γ) = n - 1 :=
            (height_eq_of_typeB c hn hgirth hG hTB1).2
          have hh : height c (e1 : c.Γ) = height c w0 :=
            congrArg (fun z : ↥(edgeBall (n - 1) c) => height c (z : c.Γ)) he
          omega
        have he2 : e2 ≠ w0' := by
          intro he
          have hheighte : height c (e2 : c.Γ) = n - 1 :=
            (height_eq_of_typeB c hn hgirth hG hTB2).2
          have hh : height c (e2 : c.Γ) = height c w0 :=
            congrArg (fun z : ↥(edgeBall (n - 1) c) => height c (z : c.Γ)) he
          omega
        exact ⟨e1, e2, hTB1, hTB2, he12, he1, he2⟩
    obtain ⟨e1, e2, hTB1, hTB2, he12, he1, he2⟩ := key
    exact ⟨w0', e1, e2, hw0adj, delta_adj_of_typeB hn hgirth hG hTB1,
      delta_adj_of_typeB hn hgirth hG hTB2, he1.symm, he2.symm, he12⟩

theorem isGenPolygon_delta (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    IsGenPolygon (delta c Good n) n := by
  obtain ⟨z, hadj, hnb, hper, hdiam⟩ := exists_periodic_polygon hn hgirth hG hdeg
  have hconn : (delta c Good n).Connected := delta_connected hn hgirth hG
  obtain ⟨col, hcol⟩ := delta_bipartite hn hgirth hG
  have hU : UniqueGeod (delta c Good n) n :=
    uniqueGeod_of_le_egirth hconn (le_egirth_delta hn hgirth hG hdeg)
  refine ⟨hconn, ⟨col, hcol⟩, ?_, ⟨z 0, z n, hdiam⟩, hU, ?_, ?_⟩
  · intro u v
    exact delta_dist_le hn hgirth hG hdeg u v
  · exact ⟨Set.range z, GPath.isPolygon_of_periodic hconn hcol (by omega) hU z hadj hnb hper⟩
  · intro u
    obtain ⟨v, w, hv, hw, hne⟩ := exists_two_delta_adj hn hgirth hG hdeg u
    calc (2 : ℕ∞) = ({v, w} : Set ↥(edgeBall (n - 1) c)).encard := (Set.encard_pair hne).symm
      _ ≤ ((delta c Good n).neighborSet u).encard := Set.encard_le_encard (by
        intro x hx
        rcases hx with rfl | rfl
        · exact hv
        · exact hw)

theorem isGeneralizedPolygon_delta (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    IsGeneralizedPolygon (delta c Good n) n :=
  isGeneralizedPolygon_of_isGenPolygon (by omega) (isGenPolygon_delta hn hgirth hG hdeg)

theorem isThick_delta [Fintype ↥(edgeBall (n - 1) c)] [DecidableRel (delta c Good n).Adj]
    (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (h3 : ∀ v w w' : c.Γ, c.graph.Adj v w → c.graph.Adj v w' →
      ∃ u, c.graph.Adj v u ∧ u ≠ w ∧ u ≠ w') :
    IsThick (delta c Good n) := by
  classical
  intro u
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := exists_three_delta_adj hn hgirth hG h3 u
  have hsub : ({a, b, d} : Finset ↥(edgeBall (n - 1) c)) ⊆
      (delta c Good n).neighborFinset u := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hd
  have hcard : ({a, b, d} : Finset ↥(edgeBall (n - 1) c)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [hab, had, hbd]
  have h3le : 3 ≤ ((delta c Good n).neighborFinset u).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  rwa [SimpleGraph.card_neighborFinset_eq_degree] at h3le

end CFSG.Quasithin.Stroth.WeissDelta

end
