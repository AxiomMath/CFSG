module

public import CFSG.Quasithin.Recognition.F4Six
public import CFSG.Quasithin.Recognition.F4Cycle

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

namespace RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y]

@[expose] def BijFirst (c : α.Completion Y) (m : ℕ) (a b : c.Γ) : Prop :=
  Set.BijOn (fun t : GPath c.graph m => t 1) (c.geods m a b) (CosetGeom.nbrs a)

structure Facts46 (c : α.Completion Y) (m : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  hm : 2 ≤ m
  uniq : ∀ (n : ℕ), n < m → ∀ (a : c.Γ) (p : GPath c.graph n), p ∈ GPath.nbPaths c.graph a n →
    c.graph.dist a (p n) = n ∧
      ∀ q : GPath c.graph n, q 0 = a → q n = p n → q.IsGeodesic → q = p
  dist_m : ∀ (a : c.Γ) (p : GPath c.graph m), p ∈ GPath.nbPaths c.graph a m →
    c.graph.dist a (p m) = m
  alt : ∀ (a : c.Γ) (p : GPath c.graph m), p ∈ GPath.nbPaths c.graph a m →
    (∀ t : GPath c.graph m, t 0 = a → t m = p m → t.IsGeodesic → t = p) ∨ BijFirst c m a (p m)
  trans_pt : ∀ a : c.Γ, CosetGeom.vtype a = false → c.PathTrans a m

end RankTwoAmalgam.Completion

namespace LieSetting

variable {S : LieSetting.{u, w}} {Y : Type w'} [Group Y] [Finite Y]

theorem Facts45L.facts46 (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful) :
    β.Facts46 S.m := by
  have hm := S.hm
  have T : β.TransComp S.m :=
    ⟨hβ, hS.thick1, hS.thick2, pathTrans_transfer β hβ S.ι S.hι (S.m + 1) hS.trans, by omega⟩
  refine ⟨hβ, hS.thick1, hS.thick2, by omega, ?_, ?_, ?_, ?_⟩
  · intro n hn a p hp
    exact ⟨T.dist_nbPath hn.le hp, fun q hq0 hqn hqg => T.unique_geod hn hp hq0 hqn hqg⟩
  · intro a p hp
    exact T.dist_nbPath le_rfl hp
  · intro a p hp
    rcases (hS.lemma_F46_8 β hβ a hp).2 with h | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro a _ q q' hq hq'
    exact GPath.trans_le T.hval (T.trans a) 1 S.m (by omega) q q' hq hq'

end LieSetting

namespace RankTwoAmalgam.Completion

theorem connected_graph {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] (c : α.Completion Y) :
    c.graph.Connected := CosetGeom.connected rfl

variable {α : RankTwoAmalgam.{u}} {Y : Type w'} [Group Y] [Finite Y] {c : α.Completion Y} {m : ℕ}
  (F : Facts46 c m)

include F

theorem Facts46.hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  exists_nbr_ne F.faithful F.thick1 F.thick2

theorem Facts46.exists_two_nbrs (v : c.Γ) :
    ∃ y₁ y₂, c.graph.Adj v y₁ ∧ c.graph.Adj v y₂ ∧ y₁ ≠ y₂ := by
  obtain ⟨y₁, h1⟩ := CosetGeom.exists_adj v
  obtain ⟨y₂, h2, hne, -⟩ := F.hval v y₁ y₁
  exact ⟨y₁, y₂, h1, h2, hne.symm⟩

omit [Finite Y] in
theorem Facts46.uniqueGeod : UniqueGeod c.graph m := by
  intro n p q hp hq h0 hn hnm
  have hpnb : p ∈ GPath.nbPaths c.graph (p 0) n :=
    ⟨rfl, GPath.noBack_of_dist_eq (connected_graph c) p hp⟩
  exact ((F.uniq n hnm (p 0) p hpnb).2 q h0.symm hn.symm hq).symm

omit [Finite Y] in
theorem Facts46.mem_geods {a : c.Γ} {p : GPath c.graph m} (hp : p ∈ GPath.nbPaths c.graph a m) :
    p ∈ c.geods m a (p m) := by
  refine ⟨hp.1, rfl, ?_⟩
  show c.graph.dist (p 0) (p m) = m
  rw [hp.1]
  exact F.dist_m a p hp

omit [Finite Y] F in
theorem Facts46.exists_geod_path {a b : c.Γ} (hab : c.graph.dist a b = m) :
    ∃ P : GPath c.graph m, P ∈ GPath.nbPaths c.graph a m ∧ P m = b := by
  obtain ⟨P, h0, hb, hnb⟩ := GPath.exists_geodesic' (connected_graph c) a b hab
  exact ⟨P, ⟨h0, hnb⟩, hb⟩

omit [Finite Y] in
theorem Facts46.mem_geods_iff {a b : c.Γ} {t : GPath c.graph m} :
    t ∈ c.geods m a b ↔ t ∈ GPath.nbPaths c.graph a m ∧ t m = b := by
  constructor
  · rintro ⟨h0, hb, hg⟩
    exact ⟨⟨h0, GPath.noBack_of_dist_eq (connected_graph c) t hg⟩, hb⟩
  · rintro ⟨hp, hb⟩
    have := F.mem_geods hp
    rwa [hb] at this

omit [Finite Y] F in
theorem exists_smul_of_vtype_false (u v : c.Γ) (hu : CosetGeom.vtype u = false)
    (hv : CosetGeom.vtype v = false) : ∃ g : c.G0, g • u = v := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq_baseVert c u
  obtain ⟨g₂, hg₂⟩ := exists_smul_eq_baseVert c v
  rw [hu] at hg₁
  rw [hv] at hg₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  have h1 : g₁⁻¹ • u = c.xv := inv_smul_eq_iff.mpr hg₁.symm
  rw [mul_smul, h1]
  exact hg₂

omit [Finite Y] in
theorem Facts46.two_geods_cycle {p q : GPath c.graph m} (hp : p.IsGeodesic) (hq : q.IsGeodesic)
    (h0 : p 0 = q 0) (hmm : p m = q m) (hne : p ≠ q) (i : ℕ) :
    ∃ t₁ t₂ : GPath c.graph m, t₁ ∈ c.geods m (GPath.cycSeq p q i) (GPath.cycSeq p q (i + m)) ∧
      t₂ ∈ c.geods m (GPath.cycSeq p q i) (GPath.cycSeq p q (i + m)) ∧ t₁ ≠ t₂ := by
  have hm := F.hm
  obtain ⟨h1, h2⟩ := GPath.geod_first_last_ne (connected_graph c) F.uniqueGeod (by omega) hp hq h0 hmm hne
  have hz := GPath.cycSeq_adj p q (by omega) h0 hmm
  have hnb := GPath.cycSeq_nb p q hm (GPath.noBack_of_dist_eq (connected_graph c) p hp)
    (GPath.noBack_of_dist_eq (connected_graph c) q hq) h0 hmm h1 h2
  have hper := GPath.cycSeq_per' p q
  have hA : GPath.arc₁ _ hz m i ∈ GPath.nbPaths c.graph (GPath.cycSeq p q i) m :=
    ⟨GPath.arc₁_zero _ hz m i, GPath.arc₁_noBack _ hz hnb m i⟩
  have hB : GPath.arc₂ _ hz m i ∈ GPath.nbPaths c.graph (GPath.cycSeq p q i) m :=
    ⟨GPath.arc₂_zero _ hz m hper i, GPath.arc₂_noBack _ hz hnb m i⟩
  refine ⟨GPath.arc₁ _ hz m i, GPath.arc₂ _ hz m i, ?_, ?_,
    GPath.arc_ne _ hz hnb m hper (by omega) i⟩
  · have := F.mem_geods hA
    rwa [GPath.arc₁_last] at this
  · have := F.mem_geods hB
    rwa [GPath.arc₂_last] at this

omit [Finite Y] in
theorem Facts46.two_geods_point (hs : c.IsSmall m) {a b : c.Γ} (ha : CosetGeom.vtype a = false)
    (hab : c.graph.dist a b = m) :
    ∃ t₁ t₂ : GPath c.graph m, t₁ ∈ c.geods m a b ∧ t₂ ∈ c.geods m a b ∧ t₁ ≠ t₂ := by
  have hm := F.hm
  obtain ⟨p, q, hp, hq, h0, hmm, hne⟩ : ∃ p q : GPath c.graph m, p.IsGeodesic ∧ q.IsGeodesic ∧
      p 0 = q 0 ∧ p m = q m ∧ p ≠ q := by
    by_contra h
    apply hs
    intro p q hp hq h0 hmm
    by_contra hne
    exact h ⟨p, q, hp, hq, h0, hmm, hne⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, CosetGeom.vtype (GPath.cycSeq p q i) = false := by
    have e0 : GPath.cycSeq p q 0 = p 0 := GPath.cycSeq_of_le p q (by omega) (Nat.zero_le m)
    have e1 : GPath.cycSeq p q 1 = p 1 := GPath.cycSeq_of_le p q (by omega) (by omega)
    have hne01 : CosetGeom.vtype (p 0) ≠ CosetGeom.vtype (p 1) :=
      CosetGeom.vtype_ne_of_adj (p.adj 0 (by omega))
    cases h : CosetGeom.vtype (p 0)
    · exact ⟨0, by rw [e0]; exact h⟩
    · refine ⟨1, ?_⟩
      rw [e1]
      cases h1 : CosetGeom.vtype (p 1)
      · rfl
      · rw [h, h1] at hne01
        exact absurd rfl hne01
  obtain ⟨t₁, t₂, ht₁, ht₂, hne12⟩ := F.two_geods_cycle hp hq h0 hmm hne i
  obtain ⟨g, hg⟩ := exists_smul_of_vtype_false (c := c) _ a hi ha
  obtain ⟨P, hP, hPb⟩ := Facts46.exists_geod_path hab
  have ht₁' := (F.mem_geods_iff).mp ht₁
  have ht₂' := (F.mem_geods_iff).mp ht₂
  have hgt₁ : g • t₁ ∈ GPath.nbPaths c.graph a m :=
    ⟨by show g • t₁ 0 = a; rw [ht₁'.1.1, hg], GPath.smul_noBack ht₁'.1.2⟩
  obtain ⟨h, hha, hht⟩ := F.trans_pt a ha (g • t₁) P hgt₁ hP
  have e1 : (h * g) • t₁ = P := by rw [GPath.mul_smul']; exact hht
  have hmem : ∀ t : GPath c.graph m,
      t ∈ c.geods m (GPath.cycSeq p q i) (GPath.cycSeq p q (i + m)) →
      (h * g) • t ∈ GPath.nbPaths c.graph a m ∧ ((h * g) • t) m = b := by
    intro t ht
    have ht' := (F.mem_geods_iff).mp ht
    refine ⟨⟨?_, GPath.smul_noBack ht'.1.2⟩, ?_⟩
    · show (h * g) • t 0 = a
      rw [ht'.1.1, mul_smul, hg, hha]
    · calc ((h * g) • t) m = (h * g) • t m := rfl
        _ = (h * g) • t₁ m := by rw [ht'.2, ht₁'.2]
        _ = ((h * g) • t₁) m := rfl
        _ = P m := by rw [e1]
        _ = b := hPb
  refine ⟨(h * g) • t₁, (h * g) • t₂, (F.mem_geods_iff).mpr (hmem t₁ ht₁),
    (F.mem_geods_iff).mpr (hmem t₂ ht₂), ?_⟩
  intro heq
  apply hne12
  have := congrArg (fun r : GPath c.graph m => (h * g)⁻¹ • r) heq
  simp only [GPath.inv_smul_smul'] at this
  exact this

theorem Facts46.lemma_F412 (hs : c.IsSmall m) (a b : c.Γ) (hab : c.graph.dist a b = m) :
    ∃ t₁ t₂ : GPath c.graph m, t₁ ∈ c.geods m a b ∧ t₂ ∈ c.geods m a b ∧ t₁ ≠ t₂ := by
  cases hv : CosetGeom.vtype a
  · exact F.two_geods_point hs hv hab
  · have hm := F.hm
    obtain ⟨r, hr, hrb⟩ := Facts46.exists_geod_path hab
    have hy1 : CosetGeom.vtype (r 1) = false := by
      have hne01 : CosetGeom.vtype (r 0) ≠ CosetGeom.vtype (r 1) :=
        CosetGeom.vtype_ne_of_adj (r.adj 0 (by omega))
      rw [hr.1, hv] at hne01
      cases h1 : CosetGeom.vtype (r 1)
      · rfl
      · rw [h1] at hne01
        exact absurd rfl hne01
    obtain ⟨y, hy, hyne, -⟩ := F.hval b (r (m - 1)) (r (m - 1))
    have hadj : c.graph.Adj (r m) y := by rw [hrb]; exact hy
    let t : GPath c.graph m := GPath.shiftSnoc r y hadj
    have ht0 : t 0 = r 1 := GPath.shiftSnoc_apply_lt r y hadj (by omega)
    have htm : t m = y := GPath.shiftSnoc_last r y hadj
    have htnb : t ∈ GPath.nbPaths c.graph (r 1) m := ⟨ht0, hr.2.shiftSnoc hadj hyne⟩
    have hdist : c.graph.dist (r 1) y = m := by
      have := F.dist_m (r 1) t htnb
      rwa [htm] at this
    obtain ⟨t₁, t₂, ht₁, ht₂, hne12⟩ := F.two_geods_point hs hy1 hdist
    rcases F.alt (r 1) t htnb with hi | hbij
    · exfalso
      apply hne12
      rw [hi t₁ ht₁.1 (by rw [ht₁.2.1, htm]) ht₁.2.2,
        hi t₂ ht₂.1 (by rw [ht₂.2.1, htm]) ht₂.2.2]
    · have ha1 : a ∈ CosetGeom.nbrs (r 1) := by
        show c.graph.Adj (r 1) a
        have := (r.adj 0 (by omega)).symm
        rwa [hr.1] at this
      obtain ⟨s, hs', hsa⟩ := hbij.2.2 ha1
      have hs'' := (F.mem_geods_iff).mp hs'
      have hsm : s m = y := by rw [hs''.2, htm]
      have hadj2 : c.graph.Adj (s m) b := by rw [hsm]; exact hy.symm
      have hst : s ≠ t := by
        intro h
        have h1 := congrArg (fun r : GPath c.graph m => r 1) h
        have e1 : t 1 = r 2 := GPath.shiftSnoc_apply_lt r y hadj (by omega)
        have : r 0 = r 2 := by rw [← hr.1] at hsa; rw [← e1, ← h1]; exact hsa.symm
        exact hr.2 0 (by omega) this
      have hsg : s.IsGeodesic := hs'.2.2
      have htg : t.IsGeodesic := by
        show c.graph.dist (t 0) (t m) = m
        rw [ht0, htm]; exact hdist
      obtain ⟨-, hlast⟩ := GPath.geod_first_last_ne (connected_graph c) F.uniqueGeod
        (by omega) hsg htg (by rw [hs''.1.1, ht0]) (by rw [hs''.2, htm]) hst
      have htlast : t (m - 1) = b := by
        rw [GPath.shiftSnoc_apply_lt r y hadj (by omega), show m - 1 + 1 = m by omega, hrb]
      have hbne : b ≠ s (m - 1) := fun h => hlast (by rw [htlast]; exact h.symm)
      let α₂ : GPath c.graph m := GPath.shiftSnoc s b hadj2
      have hα0 : α₂ 0 = a := by
        rw [GPath.shiftSnoc_apply_lt s b hadj2 (by omega)]
        exact hsa
      have hαm : α₂ m = b := GPath.shiftSnoc_last s b hadj2
      have hαnb : α₂ ∈ GPath.nbPaths c.graph a m := ⟨hα0, hs''.1.2.shiftSnoc hadj2 hbne⟩
      refine ⟨r, α₂, (F.mem_geods_iff).mpr ⟨hr, hrb⟩, (F.mem_geods_iff).mpr ⟨hαnb, hαm⟩, ?_⟩
      intro h
      have h1 := congrArg (fun r : GPath c.graph m => r 1) h
      have e1 : α₂ 1 = s 2 := GPath.shiftSnoc_apply_lt s b hadj2 (by omega)
      have e2 : r 1 = s 0 := by rw [hs''.1.1]
      have : s 0 = s 2 := by rw [← e2, ← e1]; exact h1
      exact hs''.1.2 0 (by omega) this

theorem Facts46.allBij (hs : c.IsSmall m) {a b : c.Γ} (hab : c.graph.dist a b = m) :
    BijFirst c m a b := by
  obtain ⟨P, hP, hPb⟩ := Facts46.exists_geod_path hab
  rcases F.alt a P hP with h | h
  · exfalso
    obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := F.lemma_F412 hs a b hab
    apply hne
    rw [h t₁ ht₁.1 (by rw [ht₁.2.1, hPb]) ht₁.2.2, h t₂ ht₂.1 (by rw [ht₂.2.1, hPb]) ht₂.2.2]
  · rwa [hPb] at h

end RankTwoAmalgam.Completion

end CFSG.Quasithin

