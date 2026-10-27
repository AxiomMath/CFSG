module

public import CFSG.Quasithin.Recognition.F4Basic
public import CFSG.Quasithin.Recognition.F4Paths

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

theorem end_dist (hP : IsGenPolygon Γ 8) {a : V} {n : ℕ} (hn : n ≤ 8) {p : GPath Γ n}
    (hp : p ∈ GPath.nbPaths Γ a n) : Γ.dist a (p n) = n := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have := GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod n hn p hp.2
  rw [← hp.1]
  exact this

theorem eq_of_drop_eq' {n : ℕ} (hn : 1 ≤ n) {t₁ t₂ : GPath Γ n} (h0 : t₁ 0 = t₂ 0)
    (h : t₁.drop 1 hn = t₂.drop 1 hn) : t₁ = t₂ := by
  refine GPath.ext' fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact h0
  · have := congrArg (fun t : GPath Γ (n - 1) => t (i - 1)) h
    simpa [GPath.drop_apply _ _ _ (show i - 1 ≤ n - 1 by omega),
      Nat.add_sub_cancel' hpos] using this

theorem eq_of_first_last (hP : IsGenPolygon Γ 8) {a : V} {r r' : GPath Γ 8}
    (hr : r ∈ GPath.nbPaths Γ a 8) (hr' : r' ∈ GPath.nbPaths Γ a 8) (h1 : r 1 = r' 1)
    (h8 : r 8 = r' 8) : r = r' := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have g1 : r.IsGeodesic := by
    have := GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod 8 le_rfl r hr.2
    exact this
  have g2 : r'.IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod 8 le_rfl r' hr'.2
  have d1 := GPath.IsGeodesic.drop hP.connected g1 1 (by norm_num)
  have d2 := GPath.IsGeodesic.drop hP.connected g2 1 (by norm_num)
  have e : r.drop 1 (by norm_num) = r'.drop 1 (by norm_num) := by
    refine hP.uniqueGeod (8 - 1) _ _ d1 d2 ?_ ?_ (by norm_num)
    · rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ (Nat.zero_le _)]
      exact h1
    · rw [GPath.drop_apply _ _ _ le_rfl, GPath.drop_apply _ _ _ le_rfl]
      exact h8
  exact eq_of_drop_eq' (by norm_num) (by rw [hr.1, hr'.1]) e

variable [GraphAction X Γ]

theorem smul_mem_nbPaths {a : V} {n : ℕ} {r : GPath Γ n} (hr : r ∈ GPath.nbPaths Γ a n) {g : X}
    (hg : g • a = a) : g • r ∈ GPath.nbPaths Γ a n :=
  ⟨by rw [GPath.smul_apply, hr.1, hg], GPath.smul_noBack hr.2⟩

theorem mem_stabPath_of_fix (hP : IsGenPolygon Γ 8) {a : V} {r : GPath Γ 8}
    (hr : r ∈ GPath.nbPaths Γ a 8) {k : X} (hka : k • a = a) (hk1 : k • r 1 = r 1)
    (hk8 : k • r 8 = r 8) : k ∈ (r.stabPath : Subgroup X) := by
  have e : k • r = r :=
    eq_of_first_last hP (smul_mem_nbPaths hr hka) hr (by simpa using hk1) (by simpa using hk8)
  intro i hi
  have := congrArg (fun t : GPath Γ 8 => t i) e
  simpa using this

theorem exists_base_path (hP : IsGenPolygon Γ 8) {a w b : V} (hw : Γ.Adj a w)
    (hb : Γ.dist a b = 8) : ∃ r ∈ GPath.nbPaths Γ a 8, r 1 = w ∧ r 8 = b := by
  obtain ⟨c, hc⟩ := hP.bipartite
  have hba : Γ.dist b a = 8 := by rw [SimpleGraph.dist_comm]; exact hb
  have hwb : Γ.dist b w = 7 := by
    have h1 := GPath.dist_adj_succ_or hP.connected hc b hw
    have h2 := hP.diam_le b w
    omega
  obtain ⟨g, hg0, hg7, -⟩ := GPath.exists_geodesic' hP.connected b w (n := 7) hwb
  let g' : GPath Γ 8 := g.snoc a (by rw [hg7]; exact hw.symm)
  have hg'0 : g' 0 = b := by
    have : g' 0 = g 0 := GPath.snoc_of_le _ _ _ (Nat.zero_le _)
    rw [this, hg0]
  have hg'7 : g' 7 = w := by
    have : g' 7 = g 7 := GPath.snoc_of_le _ _ _ le_rfl
    rw [this, hg7]
  have hg'8 : g' 8 = a := GPath.snoc_last _ _ _
  have hrev0 : g'.rev 0 = a := by rw [GPath.rev_apply _ (by norm_num)]; exact hg'8
  have hrev1 : g'.rev 1 = w := by rw [GPath.rev_apply _ (by norm_num)]; exact hg'7
  have hrev8 : g'.rev 8 = b := by rw [GPath.rev_apply _ le_rfl]; exact hg'0
  have hdist : Γ.dist (g'.rev 0) (g'.rev 8) = 8 := by
    rw [hrev0, hrev8]
    exact hb
  exact ⟨g'.rev, ⟨hrev0, GPath.noBack_of_dist_eq hP.connected _ hdist⟩, hrev1, hrev8⟩

end CFSG.Quasithin.TitsGeo
