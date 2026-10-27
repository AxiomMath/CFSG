module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Ball

public section

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

section GoodPaths

variable {V : Type} {H : Type} [Group H] [MulAction H V]

structure GoodPathSystem (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (n : ℕ) (Good : ∀ s : ℕ, GPath Γ s → Prop) : Prop where
  noBack : ∀ s (p : GPath Γ s), Good s p → p.NoBack
  short : ∀ s (p : GPath Γ s), s ≤ n + 1 → p.NoBack → Good s p
  take : ∀ s (p : GPath Γ s) (k : ℕ) (hk : k ≤ s), Good s p → Good k (p.take k hk)
  drop : ∀ s (p : GPath Γ s) (k : ℕ) (hk : k ≤ s), Good s p → Good (s - k) (p.drop k hk)
  rev : ∀ s (p : GPath Γ s), Good s p → Good s p.rev
  smul : ∀ s (g : H) (p : GPath Γ s), Good s p → Good s (g • p)
  extend : ∀ s (p : GPath Γ s), n + 1 ≤ s → Good s p →
    ∃! w : V, ∃ h : Γ.Adj (p s) w, Good (s + 1) (p.snoc w h)
  lemma3 : ∀ (p : GPath Γ (2 * n)) (q : GPath Γ (2 * n - 1)), Good _ p → Good _ q →
    (∀ i, i ≤ n → q i = p i) → q (n + 1) ≠ p (n + 1) →
    ∃ r : GPath Γ (2 * n - 1), Good _ r ∧ (∀ i, i ≤ n - 1 → r i = q (2 * n - 1 - i)) ∧
      (∀ i, n - 1 ≤ i → i ≤ 2 * n - 1 → r i = p (i + 1))

end GoodPaths

section Delta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]

@[expose] def TypeB (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (Good : ∀ s : ℕ, GPath c.graph s → Prop) (n : ℕ) (u v : c.Γ) : Prop :=
  ∃ p : GPath c.graph (2 * n - 1), Good _ p ∧ p 0 = u ∧ p (2 * n - 1) = v ∧
    ((p (n - 1) = c.xv ∧ p n = c.lv) ∨ (p (n - 1) = c.lv ∧ p n = c.xv))

@[expose] def delta (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (Good : ∀ s : ℕ, GPath c.graph s → Prop) (n : ℕ) : SimpleGraph ↥(edgeBall (n - 1) c) :=
  SimpleGraph.fromRel fun u v =>
    (c.graph.Adj u v ∧ ((u : c.Γ) ∈ edgeBall (n - 2) c ∨ (v : c.Γ) ∈ edgeBall (n - 2) c)) ∨
      TypeB c Good n u v

private theorem typeB_middle_rev {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
    {n : ℕ} {p : GPath c.graph (2 * n - 1)}
    (h : (p (n - 1) = c.xv ∧ p n = c.lv) ∨ (p (n - 1) = c.lv ∧ p n = c.xv)) :
    (p.rev (n - 1) = c.xv ∧ p.rev n = c.lv) ∨
      (p.rev (n - 1) = c.lv ∧ p.rev n = c.xv) := by
  have h1 : p.rev (n - 1) = p n := by
    rw [GPath.rev_apply (p := p) (i := n - 1) (by omega)]
    congr 1
    omega
  have h2 : p.rev n = p (n - 1) := by
    rw [GPath.rev_apply (p := p) (i := n) (by omega)]
    congr 1
    omega
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inr ⟨h1.trans hb, h2.trans ha⟩
  · exact Or.inl ⟨h1.trans hb, h2.trans ha⟩

private theorem height_eq_of_middle {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
    {n : ℕ} (hn : 3 ≤ n) (hconn : c.graph.Connected) (hU : UniqueGeod c.graph (n + 1))
    {p : GPath c.graph (2 * n - 1)} (hp : p.NoBack)
    (hmid : (p (n - 1) = c.xv ∧ p n = c.lv) ∨ (p (n - 1) = c.lv ∧ p n = c.xv)) :
    height c (p 0) = n - 1 := by
  have hgeo : ∀ (k : ℕ) (hk : k ≤ n + 1) (hk' : k ≤ 2 * n - 1),
      (p.take k hk').IsGeodesic := by
    intro k hk hk'
    exact GPath.isGeodesic_of_noBack (c := CosetGeom.vtype) hconn
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) hU k hk (p.take k hk') (hp.take k hk')
  have hd1 : c.graph.dist (p 0) (p (n - 1)) = n - 1 := by
    have h := hgeo (n - 1) (by omega) (by omega)
    simpa [GPath.IsGeodesic] using h
  have hd2 : c.graph.dist (p 0) (p n) = n := by
    have h := hgeo n (by omega) (by omega)
    simpa [GPath.IsGeodesic] using h
  rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hx : c.graph.dist (p 0) c.xv = n - 1 := by rw [← h1]; exact hd1
    have hy : c.graph.dist (p 0) c.lv = n := by rw [← h2]; exact hd2
    simp [height, hx, hy, min_eq_left (show n - 1 ≤ n by omega)]
  · have hy : c.graph.dist (p 0) c.lv = n - 1 := by rw [← h1]; exact hd1
    have hx : c.graph.dist (p 0) c.xv = n := by rw [← h2]; exact hd2
    simp [height, hx, hy, min_eq_right (show n - 1 ≤ n by omega)]

theorem typeB_symm (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}
    (hG : GoodPathSystem c.G0 c.graph n Good) {u v : c.Γ} (h : TypeB c Good n u v) :
    TypeB c Good n v u := by
  obtain ⟨p, hp, hp0, hpv, hmid⟩ := h
  refine ⟨p.rev, hG.rev (2 * n - 1) p hp, ?_, ?_, typeB_middle_rev hmid⟩
  · rw [GPath.rev_apply (p := p) (i := 0) (by omega), Nat.sub_zero, hpv]
  · rw [GPath.rev_apply (p := p) (i := 2 * n - 1) (by omega), Nat.sub_self, hp0]

theorem height_eq_of_typeB (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ} (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {u v : c.Γ} (h : TypeB c Good n u v) :
    height c u = n - 1 ∧ height c v = n - 1 := by
  obtain ⟨p, hp, hp0, hpv, hmid⟩ := h
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := by
    refine uniqueGeod_of_le_egirth hconn ?_
    have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
    rwa [h2]
  have hnb : p.NoBack := hG.noBack (2 * n - 1) p hp
  have hu : height c u = n - 1 := by
    rw [← hp0]
    exact height_eq_of_middle hn hconn hU hnb hmid
  have hv : height c v = n - 1 := by
    have hrev := height_eq_of_middle hn hconn hU hnb.rev (typeB_middle_rev hmid)
    rwa [GPath.rev_apply (p := p) (i := 0) (by omega), Nat.sub_zero, hpv] at hrev
  exact ⟨hu, hv⟩

end Delta

end CFSG.Quasithin.Stroth.WeissDelta

end
