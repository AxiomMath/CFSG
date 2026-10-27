module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoFacts46
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y} {k : ℕ}

theorem burnsideF46_hval (T : TitsHyp c k) : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval T.faithful T.thick1 T.thick2

theorem burnsideF46_pt_F35 (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = false)
    {p : GPath c.graph (k + 2)} (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) :
    GPath.F35Conclusion c.graph c.G0 a (k + 1) p :=
  GPath.lemma_F35 (burnsideF46_hval T) (T.transPt a ha) (connected_graph c) (hbip c)
    (by have := T.hk; omega) hp

theorem burnsideF46_ln_F35 (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = true)
    {p : GPath c.graph (k + 1)} (hp : p ∈ GPath.nbPaths c.graph a (k + 1)) :
    GPath.F35Conclusion c.graph c.G0 a k p :=
  GPath.lemma_F35 (burnsideF46_hval T) (T.transLn a ha) (connected_graph c) (hbip c) T.hk hp

theorem burnsideF46_pt_dist (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = false) {i : ℕ}
    (hi : i ≤ k + 1) {q : GPath c.graph i} (hq : q ∈ GPath.nbPaths c.graph a i) :
    c.graph.dist a (q i) = i := by
  obtain ⟨p, hp⟩ := GPath.exists_nbPaths (burnsideF46_hval T) a (k + 2)
  exact (burnsideF46_pt_F35 T ha hp).2.1 i hi q hq

theorem burnsideF46_pt_end (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = false)
    {p : GPath c.graph (k + 2)} (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) :
    c.graph.dist a (p (k + 2)) = k + 2 :=
  (burnsideF46_pt_F35 T ha hp).2.2.2.2.2.2 (fun y hy hne => T.noFix a ha p hp y hy hne)

theorem burnsideF46_pt_uniq (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = false) {n : ℕ}
    (hn : n < k + 2) {r : GPath c.graph n} (hr : r ∈ GPath.nbPaths c.graph a n)
    {t : GPath c.graph n} (ht0 : t 0 = a) (htn : t n = r n) (htg : t.IsGeodesic) : t = r := by
  obtain ⟨p, hp, hpr⟩ := GPath.exists_extend_to (burnsideF46_hval T) (show n ≤ k + 2 by omega) hr
  have hF := burnsideF46_pt_F35 T ha hp
  rcases Nat.lt_or_ge n (k + 1) with h1 | h1
  · have := hF.2.2.2.1 n h1 t ht0 (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl]) htg
    rw [this, hpr]
  · have hn1 : n = k + 1 := by omega
    subst hn1
    rcases hF.2.2.2.2.2.1 with h3 | ⟨hd, -⟩
    · have := (h3 p hp).2 t ht0 htg (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl])
      rw [this, hpr]
    · exfalso
      have := burnsideF46_pt_end T ha hp
      have := hd (p (k + 2))
      omega

theorem burnsideF46_ln_end (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = true)
    {p : GPath c.graph (k + 1)} (hp : p ∈ GPath.nbPaths c.graph a (k + 1)) :
    c.graph.dist a (p (k + 1)) = k + 1 := by
  have hb : CosetGeom.vtype (p (k + 1)) = false := by
    rw [vtype_path_odd p le_rfl T.even.add_one, hp.1, ha]
    rfl
  have h := burnsideF46_pt_dist T hb le_rfl (rev_mem_nbPaths hp)
  rw [rev_apply_last, hp.1] at h
  rw [SimpleGraph.dist_comm]
  exact h

theorem burnsideF46_ln_uniq (T : TitsHyp c k) {a : c.Γ} (ha : CosetGeom.vtype a = true) {n : ℕ}
    (hn : n < k + 2) {r : GPath c.graph n} (hr : r ∈ GPath.nbPaths c.graph a n)
    {t : GPath c.graph n} (ht0 : t 0 = a) (htn : t n = r n) (htg : t.IsGeodesic) : t = r := by
  rcases Nat.lt_or_ge n (k + 1) with h1 | h1
  · obtain ⟨p, hp, hpr⟩ := GPath.exists_extend_to (burnsideF46_hval T)
      (show n ≤ k + 1 by omega) hr
    have hF := burnsideF46_ln_F35 T ha hp
    rcases Nat.lt_or_ge n k with h2 | h2
    · have := hF.2.2.2.1 n h2 t ht0 (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl]) htg
      rw [this, hpr]
    · have hnk : k = n := by omega
      subst hnk
      rcases hF.2.2.2.2.2.1 with h3 | ⟨hd, -⟩
      · have := (h3 p hp).2 t ht0 htg (by rw [htn, ← hpr, GPath.take_apply_of_le _ _ _ le_rfl])
        rw [this, hpr]
      · exfalso
        have := burnsideF46_ln_end T ha hp
        have := hd (p (k + 1))
        omega
  · have hn1 : n = k + 1 := by omega
    subst hn1
    have hb : CosetGeom.vtype (r (k + 1)) = false := by
      rw [vtype_path_odd r le_rfl T.even.add_one, hr.1, ha]
      rfl
    have hu := burnsideF46_pt_uniq T hb (show k + 1 < k + 2 by omega) (rev_mem_nbPaths hr)
      (t := t.rev) (by rw [GPath.rev_apply _ (Nat.zero_le _), Nat.sub_zero, htn])
      (by rw [rev_apply_last, rev_apply_last, ht0, hr.1]) htg.rev
    rw [← GPath.rev_rev t, hu, GPath.rev_rev]

theorem burnsideF46_uniq_all (T : TitsHyp c k) {a : c.Γ} {n : ℕ} (hn : n < k + 2)
    {p : GPath c.graph n} (hp : p ∈ GPath.nbPaths c.graph a n) :
    c.graph.dist a (p n) = n ∧
      ∀ q : GPath c.graph n, q 0 = a → q n = p n → q.IsGeodesic → q = p := by
  cases ha : CosetGeom.vtype a
  · exact ⟨burnsideF46_pt_dist T ha (by omega) hp,
      fun q hq0 hqn hqg => burnsideF46_pt_uniq T ha hn hp hq0 hqn hqg⟩
  · refine ⟨?_, fun q hq0 hqn hqg => burnsideF46_ln_uniq T ha hn hp hq0 hqn hqg⟩
    rcases Nat.lt_or_ge n (k + 1) with h1 | h1
    · obtain ⟨p', hp'⟩ := GPath.exists_nbPaths (burnsideF46_hval T) a (k + 1)
      exact (burnsideF46_ln_F35 T ha hp').2.1 n (by omega) p hp
    · have hn1 : n = k + 1 := by omega
      subst hn1
      exact burnsideF46_ln_end T ha hp

theorem burnsideF46_dist_m_all (T : TitsHyp c k) {a : c.Γ} {p : GPath c.graph (k + 2)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) : c.graph.dist a (p (k + 2)) = k + 2 := by
  cases ha : CosetGeom.vtype a
  · exact burnsideF46_pt_end T ha hp
  · have hconn := connected_graph c
    have htake : p.take (k + 1) (by omega) ∈ GPath.nbPaths c.graph a (k + 1) :=
      ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hp.1, hp.2.take _ _⟩
    have h1 : c.graph.dist a (p (k + 1)) = k + 1 := by
      have := burnsideF46_ln_end T ha htake
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
    have heq := burnsideF46_ln_uniq T ha (show k + 1 < k + 2 by omega) htake (t := g') hg'0
      (by rw [hg'e, GPath.take_apply_of_le _ _ _ le_rfl]) hg'g
    have hk := congrArg (fun t : GPath c.graph (k + 1) => t k) heq
    simp only [GPath.take_apply_of_le _ _ _ (Nat.le_succ k)] at hk
    have hgk' : g' k = p (k + 2) := by
      show g.snoc _ _ k = _
      rw [GPath.snoc_of_le _ _ _ le_rfl, hgk]
    rw [hgk'] at hk
    exact hp.2 k (by omega) hk.symm

theorem burnsideF46_alt_all (T : TitsHyp c k) {a : c.Γ} {p : GPath c.graph (k + 2)}
    (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) :
    (∀ t : GPath c.graph (k + 2), t 0 = a → t (k + 2) = p (k + 2) → t.IsGeodesic → t = p) ∨
      BijFirst c (k + 2) a (p (k + 2)) := by
  by_cases huniq : ∀ t : GPath c.graph (k + 2), t 0 = a → t (k + 2) = p (k + 2) →
      t.IsGeodesic → t = p
  · exact Or.inl huniq
  · right
    push Not at huniq
    obtain ⟨q, hq0, hqm, hqg, hqne⟩ := huniq
    have hconn := connected_graph c
    have hpg : p.IsGeodesic := by
      show c.graph.dist (p 0) (p (k + 2)) = k + 2
      rw [hp.1]
      exact burnsideF46_dist_m_all T hp
    have hq : q ∈ GPath.nbPaths c.graph a (k + 2) :=
      ⟨hq0, GPath.noBack_of_dist_eq hconn q hqg⟩
    have hdrop : ∀ t : GPath c.graph (k + 2), t ∈ c.geods (k + 2) a (p (k + 2)) →
        t.drop 1 (by omega) ∈ GPath.nbPaths c.graph (t 1) (k + 1) := by
      intro t ht
      have hg := GPath.IsGeodesic.drop hconn ht.2.2 1 (by omega)
      refine ⟨by rw [GPath.drop_apply _ _ _ (Nat.zero_le _), add_zero], ?_⟩
      exact GPath.noBack_of_dist_eq hconn _ hg
    have hinj : ∀ t₁ ∈ c.geods (k + 2) a (p (k + 2)), ∀ t₂ ∈ c.geods (k + 2) a (p (k + 2)),
        t₁ 1 = t₂ 1 → t₁ = t₂ := by
      intro t₁ ht₁ t₂ ht₂ h1
      have hu := (burnsideF46_uniq_all T (a := t₁ 1) (n := k + 1) (by omega) (hdrop t₁ ht₁)).2
        (t₂.drop 1 (by omega)) (by
          rw [GPath.drop_apply _ _ _ (Nat.zero_le _), add_zero, h1]) (by
          rw [GPath.drop_apply _ _ _ (show k + 1 ≤ k + 2 - 1 by omega),
            GPath.drop_apply _ _ _ (show k + 1 ≤ k + 2 - 1 by omega)]
          rw [show 1 + (k + 1) = k + 2 by omega, ht₁.2.1, ht₂.2.1])
        (GPath.IsGeodesic.drop hconn ht₂.2.2 1 (by omega))
      exact eq_of_drop_eq (by omega) (by rw [ht₁.1, ht₂.1]) hu.symm
    have hpmem : p ∈ c.geods (k + 2) a (p (k + 2)) := ⟨hp.1, rfl, hpg⟩
    have hqmem : q ∈ c.geods (k + 2) a (p (k + 2)) := ⟨hq0, hqm, hqg⟩
    have hne : p 1 ≠ q 1 := fun h => hqne (hinj q hqmem p hpmem h.symm)
    refine ⟨fun t ht => ?_, fun t₁ ht₁ t₂ ht₂ h => hinj t₁ ht₁ t₂ ht₂ h, fun y hy => ?_⟩
    · show c.graph.Adj a (t 1)
      rw [← ht.1]
      exact t.adj 0 (by omega)
    · obtain ⟨g, hg, hgy⟩ := T.pair a p hp q hq hne (p 1) y
        (by rw [← hp.1]; exact p.adj 0 (by omega)) hy
      have hle : (p.stabPath : Subgroup c.G0) ⊔ q.stabPath ≤
          MulAction.stabilizer c.G0 a ⊓ MulAction.stabilizer c.G0 (p (k + 2)) :=
        sup_le (stabPath_le_stab_ends hp.1 rfl) (stabPath_le_stab_ends hq0 hqm)
      have hga := MulAction.mem_stabilizer_iff.mp (hle hg).1
      have hgb := MulAction.mem_stabilizer_iff.mp (hle hg).2
      refine ⟨g • p, ⟨?_, ?_, hpg.smul hconn g⟩, hgy⟩
      · show g • p 0 = a
        rw [hp.1, hga]
      · show g • p (k + 2) = p (k + 2)
        exact hgb

theorem burnsideF46_facts46 (T : TitsHyp c k) : c.Facts46 (k + 2) where
  faithful := T.faithful
  thick1 := T.thick1
  thick2 := T.thick2
  hm := by have := T.hk; omega
  uniq n hn a p hp := burnsideF46_uniq_all T hn hp
  dist_m a p hp := burnsideF46_dist_m_all T hp
  alt a p hp := burnsideF46_alt_all T hp
  trans_pt a ha := T.transPt a ha

end CFSG.ASVolI
