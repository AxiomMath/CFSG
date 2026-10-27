module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPts

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

namespace TitsHyp

variable {c : α.Completion Y} [Finite Y] {k : ℕ} (T : TitsHyp c k)

include T

theorem ln_end {a : c.Γ} (ha : CosetGeom.vtype a = true) {p : GPath c.graph (k + 1)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 1)) : c.graph.dist a (p (k + 1)) = k + 1 := by
  have hb : CosetGeom.vtype (p (k + 1)) = false := by
    rw [vtype_path_odd p le_rfl T.even.add_one, hp.1, ha]
    rfl
  have h := T.pt_dist hb le_rfl (rev_mem_nbPaths hp)
  rw [rev_apply_last, hp.1] at h
  rw [SimpleGraph.dist_comm]
  exact h

theorem ln_uniq {a : c.Γ} (ha : CosetGeom.vtype a = true) {n : ℕ} (hn : n < k + 2)
    {r : GPath c.graph n} (hr : r ∈ GPath.nbPaths c.graph a n) {t : GPath c.graph n}
    (ht0 : t 0 = a) (htn : t n = r n) (htg : t.IsGeodesic) : t = r := by
  rcases Nat.lt_or_ge n (k + 1) with h1 | h1
  · obtain ⟨p, hp, hpr⟩ := GPath.exists_extend_to T.hval (show n ≤ k + 1 by omega) hr
    have hF := T.ln_F35 ha hp
    rcases Nat.lt_or_ge n k with h2 | h2
    · have := hF.2.2.2.1 n h2 t ht0 (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl]) htg
      rw [this, hpr]
    · have hnk : k = n := by omega
      subst hnk
      rcases hF.2.2.2.2.2.1 with h3 | ⟨hd, -⟩
      · have := (h3 p hp).2 t ht0 htg (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl])
        rw [this, hpr]
      · exfalso
        have := T.ln_end ha hp
        have := hd (p (k + 1))
        omega
  · have hn1 : n = k + 1 := by omega
    subst hn1
    have hb : CosetGeom.vtype (r (k + 1)) = false := by
      rw [vtype_path_odd r le_rfl T.even.add_one, hr.1, ha]
      rfl
    have hu := T.pt_uniq hb (show k + 1 < k + 2 by omega) (rev_mem_nbPaths hr) (t := t.rev)
      (by rw [GPath.rev_apply _ (Nat.zero_le _), Nat.sub_zero, htn])
      (by rw [rev_apply_last, rev_apply_last, ht0, hr.1]) htg.rev
    rw [← GPath.rev_rev t, hu, GPath.rev_rev]

theorem uniq_all {a : c.Γ} {n : ℕ} (hn : n < k + 2) {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) :
    c.graph.dist a (p n) = n ∧
      ∀ q : GPath c.graph n, q 0 = a → q n = p n → q.IsGeodesic → q = p := by
  cases ha : CosetGeom.vtype a
  · exact ⟨T.pt_dist ha (by omega) hp, fun q hq0 hqn hqg => T.pt_uniq ha hn hp hq0 hqn hqg⟩
  · refine ⟨?_, fun q hq0 hqn hqg => T.ln_uniq ha hn hp hq0 hqn hqg⟩
    rcases Nat.lt_or_ge n (k + 1) with h1 | h1
    · obtain ⟨p', hp'⟩ := GPath.exists_nbPaths T.hval a (k + 1)
      exact (T.ln_F35 ha hp').2.1 n (by omega) p hp
    · have hn1 : n = k + 1 := by omega
      subst hn1
      exact T.ln_end ha hp

theorem dist_m_all {a : c.Γ} {p : GPath c.graph (k + 2)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) : c.graph.dist a (p (k + 2)) = k + 2 := by
  cases ha : CosetGeom.vtype a
  · exact T.pt_end ha hp
  · have hconn := connected_graph c
    have htake : p.take (k + 1) (by omega) ∈ GPath.nbPaths c.graph a (k + 1) :=
      ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hp.1, hp.2.take _ _⟩
    have h1 : c.graph.dist a (p (k + 1)) = k + 1 := by
      have := T.ln_end ha htake
      rwa [GPath.take_apply_of_le _ _ _ le_rfl] at this
    have hle : c.graph.dist (p 0) (p (k + 2)) ≤ k + 2 := GPath.dist_le_length hconn p
    rw [hp.1] at hle
    have hadj : c.graph.Adj (p (k + 2)) (p (k + 1)) := (p.adj (k + 1) (by omega)).symm
    have h2 : c.graph.dist a (p (k + 1)) ≤ c.graph.dist a (p (k + 2)) + 1 := by
      have := hconn.dist_triangle (u := a) (v := p (k + 2)) (w := p (k + 1))
      have h3 : c.graph.dist (p (k + 2)) (p (k + 1)) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      omega
    have hev : Even (c.graph.dist a (p (k + 2))) := by
      have e1 := vtype_path_even p (show k + 2 ≤ k + 2 by omega) (T.even.add (by decide))
      rw [hp.1, ha] at e1
      exact (GPath.dist_even_iff hconn (hbip c) a (p (k + 2))).mp (by rw [ha, e1])
    obtain ⟨r, hr⟩ := T.even
    obtain ⟨s, hs⟩ := hev
    by_contra hne
    have hdk : c.graph.dist a (p (k + 2)) = k := by omega
    obtain ⟨g, hg0, hgk, hgnb⟩ := GPath.exists_geodesic' hconn a (p (k + 2)) hdk
    let g' : GPath c.graph (k + 1) := g.snoc (p (k + 1)) (by rw [hgk]; exact hadj)
    have hg'0 : g' 0 = a := by
      show g.snoc _ _ 0 = a
      rw [GPath.snoc_of_le _ _ _ (Nat.zero_le _), hg0]
    have hg'e : g' (k + 1) = p (k + 1) := GPath.snoc_last _ _ _
    have hg'g : g'.IsGeodesic := by
      show c.graph.dist (g' 0) (g' (k + 1)) = k + 1
      rw [hg'0, hg'e]
      exact h1
    have heq := T.ln_uniq ha (show k + 1 < k + 2 by omega) htake (t := g') hg'0
      (by rw [hg'e, GPath.take_apply_of_le _ _ _ le_rfl]) hg'g
    have hk := congrArg (fun t : GPath c.graph (k + 1) => t k) heq
    simp only [GPath.take_apply_of_le _ _ _ (Nat.le_succ k)] at hk
    have hgk' : g' k = p (k + 2) := by
      show g.snoc _ _ k = _
      rw [GPath.snoc_of_le _ _ _ le_rfl, hgk]
    rw [hgk'] at hk
    exact hp.2 k (by omega) hk.symm

end TitsHyp

end CFSG.Quasithin.TitsGeo
