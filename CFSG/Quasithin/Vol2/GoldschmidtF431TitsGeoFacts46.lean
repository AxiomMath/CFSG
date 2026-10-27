module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLns

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

theorem eq_of_drop_eq {c : α.Completion Y} {n : ℕ} (hn : 1 ≤ n) {t₁ t₂ : GPath c.graph n}
    (h0 : t₁ 0 = t₂ 0) (h : t₁.drop 1 hn = t₂.drop 1 hn) : t₁ = t₂ := by
  refine GPath.ext' fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact h0
  · have := congrArg (fun t : GPath c.graph (n - 1) => t (i - 1)) h
    simpa [GPath.drop_apply _ _ _ (show i - 1 ≤ n - 1 by omega),
      Nat.add_sub_cancel' hpos] using this

theorem stabPath_le_stab_ends {c : α.Completion Y} {n : ℕ} {a b : c.Γ} {p : GPath c.graph n}
    (h0 : p 0 = a) (hn : p n = b) :
    (p.stabPath : Subgroup c.G0) ≤ MulAction.stabilizer c.G0 a ⊓ MulAction.stabilizer c.G0 b := by
  intro g hg
  rw [GPath.mem_stabPath_iff] at hg
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, ← h0]
    exact hg 0 (Nat.zero_le n)
  · rw [MulAction.mem_stabilizer_iff, ← hn]
    exact hg n le_rfl

namespace TitsHyp

variable {c : α.Completion Y} [Finite Y] {k : ℕ} (T : TitsHyp c k)

include T

theorem alt_all {a : c.Γ} {p : GPath c.graph (k + 2)} (hp : p ∈ GPath.nbPaths c.graph a (k + 2)) :
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
      exact T.dist_m_all hp
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
      have hu := (T.uniq_all (a := t₁ 1) (n := k + 1) (by omega) (hdrop t₁ ht₁)).2
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

theorem facts46 : c.Facts46 (k + 2) where
  faithful := T.faithful
  thick1 := T.thick1
  thick2 := T.thick2
  hm := by have := T.hk; omega
  uniq n hn a p hp := T.uniq_all hn hp
  dist_m a p hp := T.dist_m_all hp
  alt a p hp := T.alt_all hp
  trans_pt a ha := T.transPt a ha

end TitsHyp

end CFSG.Quasithin.TitsGeo
