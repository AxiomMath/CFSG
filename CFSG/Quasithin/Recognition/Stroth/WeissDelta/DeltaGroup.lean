module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Hat2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RootGroups

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

@[expose] def deltaAut (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (Good : ∀ s : ℕ, GPath c.graph s → Prop) (n : ℕ) :
    Subgroup (Equiv.Perm ↥(edgeBall (n - 1) c)) where
  carrier := {f | ∀ u v, (delta c Good n).Adj (f u) (f v) ↔ (delta c Good n).Adj u v}
  one_mem' := by
    intro u v
    simp
  mul_mem' := by
    intro f g hf hg u v
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact (hf (g u) (g v)).trans (hg u v)
  inv_mem' := by
    intro f hf u v
    have h := hf (f.symm u) (f.symm v)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm

theorem mem_deltaAut_iff {f : Equiv.Perm ↥(edgeBall (n - 1) c)} :
    f ∈ deltaAut c Good n ↔
      ∀ u v, (delta c Good n).Adj (f u) (f v) ↔ (delta c Good n).Adj u v :=
  Iff.rfl

theorem delta_unfold {u v : ↥(edgeBall (n - 1) c)} :
    (delta c Good n).Adj u v ↔
      u ≠ v ∧
        (((c.graph.Adj (u : c.Γ) (v : c.Γ) ∧
            ((u : c.Γ) ∈ edgeBall (n - 2) c ∨ (v : c.Γ) ∈ edgeBall (n - 2) c)) ∨
            TypeB c Good n u v) ∨
          ((c.graph.Adj (v : c.Γ) (u : c.Γ) ∧
            ((v : c.Γ) ∈ edgeBall (n - 2) c ∨ (u : c.Γ) ∈ edgeBall (n - 2) c)) ∨
            TypeB c Good n v u)) := by
  rw [delta, SimpleGraph.fromRel_adj]

theorem hatX_mem_deltaAut (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) :
    hatX hn hgirth hG a ∈ deltaAut c Good n :=
  fun u v => hatX_adj hn hgirth hG a

theorem hatY_mem_deltaAut (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) :
    hatY hn hgirth hG a ∈ deltaAut c Good n :=
  fun u v => hatY_adj hn hgirth hG a

theorem height_eq_min_dist {z z' w : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) {a b : ℕ}
    (h1 : c.graph.dist z w = a) (h2 : c.graph.dist z' w = b) :
    height c w = min a b := by
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [height, SimpleGraph.dist_comm (u := w) (v := c.xv),
      SimpleGraph.dist_comm (u := w) (v := c.lv), h1, h2]
  · rw [height, SimpleGraph.dist_comm (u := w) (v := c.xv),
      SimpleGraph.dist_comm (u := w) (v := c.lv), h1, h2, min_comm]

private theorem mem_edgeBall_of_height_le {z z' w : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) {r : ℕ}
    (h : height c w ≤ r) : w ∈ edgeBall r c := by
  rw [mem_edgeBall_iff hz]
  have hmin : min (c.graph.dist w c.xv) (c.graph.dist w c.lv) ≤ r := by
    simpa [height] using h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases min_le_iff.mp hmin with h' | h'
    · exact Or.inl (by rwa [SimpleGraph.dist_comm])
    · exact Or.inr (by rwa [SimpleGraph.dist_comm])
  · rcases min_le_iff.mp hmin with h' | h'
    · exact Or.inr (by rwa [SimpleGraph.dist_comm])
    · exact Or.inl (by rwa [SimpleGraph.dist_comm])

private theorem dist_base_le_height_succ {z z' w : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv)) {r : ℕ}
    (h : height c w ≤ r) : c.graph.dist z w ≤ r + 1 := by
  have hpar := dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) w
  have hmin : min (c.graph.dist w c.xv) (c.graph.dist w c.lv) ≤ r := by
    simpa [height] using h
  have hboth : c.graph.dist w c.xv ≤ r + 1 ∧ c.graph.dist w c.lv ≤ r + 1 := by
    rcases hpar with hp | hp
    · have hle : c.graph.dist w c.lv ≤ r := by
        rw [min_eq_right (by omega : c.graph.dist w c.lv ≤ c.graph.dist w c.xv)] at hmin
        exact hmin
      omega
    · have hle : c.graph.dist w c.xv ≤ r := by
        rw [min_eq_left (by omega : c.graph.dist w c.xv ≤ c.graph.dist w c.lv)] at hmin
        exact hmin
      omega
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [SimpleGraph.dist_comm]
    exact hboth.1
  · rw [SimpleGraph.dist_comm]
    exact hboth.2

private theorem height_eq_of_dist_pair {z z' w : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (h1 : c.graph.dist z w = n) (h2 : c.graph.dist z' w = n - 1) :
    height c w = n - 1 := by
  rw [height_eq_min_dist hz h1 h2, min_eq_right (by omega)]

private theorem dist_right_of_height (hn : 1 ≤ n) {z z' v : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (hh : height c v = n - 1) (hv : c.graph.dist z v = n - 1) :
    c.graph.dist z' v = n := by
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hvx : c.graph.dist v c.xv = n - 1 := by rw [SimpleGraph.dist_comm]; exact hv
    have hmin : min (c.graph.dist v c.xv) (c.graph.dist v c.lv) = n - 1 := by
      simpa [height] using hh
    rw [hvx] at hmin
    have hle : n - 1 ≤ c.graph.dist v c.lv := by
      rw [← hmin]
      exact min_le_right _ _
    rcases dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) v with h | h
    · rw [hvx] at h
      omega
    · rw [hvx] at h
      calc c.graph.dist c.lv v = c.graph.dist v c.lv := SimpleGraph.dist_comm ..
        _ = n := by omega
  · have hvl : c.graph.dist v c.lv = n - 1 := by rw [SimpleGraph.dist_comm]; exact hv
    have hmin : min (c.graph.dist v c.xv) (c.graph.dist v c.lv) = n - 1 := by
      simpa [height] using hh
    rw [hvl] at hmin
    have hle : n - 1 ≤ c.graph.dist v c.xv := by
      rw [← hmin]
      exact min_le_left _ _
    rcases dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) v with h | h
    · rw [hvl] at h
      calc c.graph.dist c.xv v = c.graph.dist v c.xv := SimpleGraph.dist_comm ..
        _ = n := by omega
    · rw [hvl] at h
      omega

private theorem typeB_middle_of_dist (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {z z' v w : c.Γ}
    (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    (hv : c.graph.dist z v = n - 1) (hw : c.graph.dist z w = n)
    {p : GPath c.graph (2 * n - 1)} (hp : Good (2 * n - 1) p)
    (hp0 : p 0 = v) (hpw : p (2 * n - 1) = w)
    (hmid : (p (n - 1) = z ∧ p n = z') ∨ (p (n - 1) = z' ∧ p n = z)) :
    p (n - 1) = z ∧ p n = z' := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hc : ∀ a b, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  by_contra hcon
  have h2 : p (n - 1) = z' ∧ p n = z := by
    rcases hmid with h | h
    · exact absurd h hcon
    · exact h
  have hnb : p.NoBack := hG.noBack _ p hp
  have hpre : (p.take (n - 1) (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) _ (hnb.take _ _)
  have hdist : c.graph.dist v z' = n - 1 := by
    have h := hpre
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
      GPath.take_apply_of_le _ _ _ le_rfl, hp0, h2.1] at h
    exact h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hvx : c.graph.dist v c.xv = n - 1 := by rw [SimpleGraph.dist_comm]; exact hv
    have hpar := dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) v
    rw [hvx] at hpar
    rw [SimpleGraph.dist_comm (u := v) (v := c.lv)] at hpar
    rw [SimpleGraph.dist_comm] at hdist
    omega
  · have hvl : c.graph.dist v c.lv = n - 1 := by rw [SimpleGraph.dist_comm]; exact hv
    have hpar := dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) v
    rw [hvl] at hpar
    rw [SimpleGraph.dist_comm (u := v) (v := c.xv)] at hpar
    rw [SimpleGraph.dist_comm] at hdist
    omega

theorem exists_typeB_of_far (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    {z z' : c.Γ} (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    {u : c.Γ} (hu : u ∈ edgeBall (n - 1) c)
    (hfar : ¬ c.graph.dist z u ≤ n - 1) :
    ∃ v : c.Γ, TypeB c Good n u v ∧ c.graph.dist z v = n - 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hc : ∀ a b, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  obtain ⟨hdz, hdz'⟩ := dist_eq_of_far hn hz hu hfar
  obtain ⟨w, hzw, hwz'⟩ := hdeg z z' (adj_base_edge hz)
  obtain ⟨g, hg0, hgN, hgnb⟩ := GPath.exists_geodesic' (n := n - 1) hconn u z' (by
    rw [SimpleGraph.dist_comm]; exact hdz')
  have hggeo : g.IsGeodesic := by
    change c.graph.dist (g 0) (g (n - 1)) = n - 1
    rw [hg0, hgN, SimpleGraph.dist_comm]
    exact hdz'
  have h1 : c.graph.Adj (g (n - 1)) z := by
    rw [hgN]
    exact (adj_base_edge hz).symm
  have hgnb' : (g.snoc z h1).NoBack := by
    refine GPath.noBack_snoc hgnb h1 ?_
    intro _
    intro heq
    have hdist := hggeo.dist_eq hconn (j := n - 2) (by omega)
    rw [hg0] at hdist
    have huz : c.graph.dist u z = n - 2 := by rw [heq]; exact hdist
    rw [SimpleGraph.dist_comm (u := u) (v := z)] at huz
    rw [hdz] at huz
    omega
  have h2adj : c.graph.Adj ((g.snoc z h1) ((n - 1) + 1)) w := by
    rw [GPath.snoc_last]
    exact hzw
  let q0 : GPath c.graph (n + 1) :=
    GPath.castLength (by omega : (n - 1) + 1 + 1 = n + 1)
      ((g.snoc z h1).snoc w h2adj)
  have hq0nb : q0.NoBack := by
    refine GPath.castLength_noBack _ ?_
    refine GPath.noBack_snoc hgnb' h2adj ?_
    intro _
    intro heq
    have heq' : w = z' := by
      rw [show (n - 1) + 1 - 1 = n - 1 by omega,
        GPath.snoc_of_le _ _ _ le_rfl, hgN] at heq
      exact heq
    exact hwz' heq'
  have hq0good : Good (n + 1) q0 := hG.short (n + 1) q0 le_rfl hq0nb
  obtain ⟨p, ⟨hpgood, hpeq⟩, -⟩ :=
    hG.existsUnique_extendTo (s := n + 1) (t := 2 * n - 1)
      q0 le_rfl (by omega) hq0good
  have hq01 : q0 (n - 1) = z' := by
    rw [show q0 (n - 1) = ((g.snoc z h1).snoc w h2adj) (n - 1) from rfl,
      GPath.snoc_of_le _ _ _ (by omega : n - 1 ≤ (n - 1) + 1),
      GPath.snoc_of_le _ _ _ le_rfl, hgN]
  have hq0n : q0 n = z := by
    rw [show q0 n = ((g.snoc z h1).snoc w h2adj) n from rfl,
      GPath.snoc_of_le _ _ _ (by omega : n ≤ (n - 1) + 1)]
    calc (g.snoc z h1) n = (g.snoc z h1) ((n - 1) + 1) :=
          congrArg (fun k => (g.snoc z h1).toFun k) (show n = (n - 1) + 1 by omega)
      _ = z := GPath.snoc_last g z h1
  have hpmid : p (n - 1) = z' ∧ p n = z := by
    constructor
    · rw [hpeq (n - 1) (by omega)]
      exact hq01
    · rw [hpeq n (by omega)]
      exact hq0n
  refine ⟨p (2 * n - 1), ⟨p, hpgood, ?_, rfl, ?_⟩, ?_⟩
  · rw [hpeq 0 (by omega),
      show q0 0 = ((g.snoc z h1).snoc w h2adj) 0 from rfl,
      GPath.snoc_of_le _ _ _ (by omega : 0 ≤ (n - 1) + 1),
      GPath.snoc_of_le _ _ _ (by omega : 0 ≤ n - 1)]
    exact hg0
  · rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr hpmid
    · exact Or.inl hpmid
  · have hdrop : (p.drop n (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack hconn hc hU (2 * n - 1 - n) (by omega) _
        (GPath.NoBack.drop (hG.noBack _ p hpgood) n (by omega))
    rw [GPath.IsGeodesic, GPath.drop_apply _ _ _ (Nat.zero_le _),
      GPath.drop_apply _ _ _ le_rfl, Nat.add_zero] at hdrop
    rw [hpmid.2] at hdrop
    rw [show n + (2 * n - 1 - n) = 2 * n - 1 by omega,
      show 2 * n - 1 - n = n - 1 by omega] at hdrop
    exact hdrop

private theorem dist_penultimate_of_good (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {z z' w : c.Γ}
    (hw : c.graph.dist z w = n)
    {p : GPath c.graph (2 * n - 1)} (hp : Good (2 * n - 1) p)
    (hpw : p (2 * n - 1) = w) (hmid : p (n - 1) = z ∧ p n = z') :
    c.graph.dist z (p (2 * n - 2)) = n - 1 ∧
      c.graph.dist z' (p (2 * n - 2)) = n - 2 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hc : ∀ a b, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  have hnb : p.NoBack := hG.noBack _ p hp
  have hgeo : ((p.drop n (by omega)).take (n - 2) (by omega)).IsGeodesic :=
    GPath.isGeodesic_of_noBack hconn hc hU (n - 2) (by omega) _
      ((hnb.drop n (by omega)).take (n - 2) (by omega))
  have hz' : c.graph.dist z' (p (2 * n - 2)) = n - 2 := by
    have h := hgeo
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
      GPath.take_apply_of_le _ _ _ le_rfl,
      GPath.drop_apply _ _ _ (Nat.zero_le _),
      GPath.drop_apply _ _ _ (by omega : n - 2 ≤ 2 * n - 1 - n), Nat.add_zero,
      hmid.2] at h
    rwa [show n + (n - 2) = 2 * n - 2 by omega] at h
  have hle : c.graph.dist z (p (2 * n - 2)) ≤ n - 1 := by
    have hgeo2 : ((p.drop (n - 1) (by omega)).take (n - 1) (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) _
        ((hnb.drop (n - 1) (by omega)).take (n - 1) (by omega))
    have h := hgeo2
    rw [GPath.IsGeodesic, GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
      GPath.take_apply_of_le _ _ _ le_rfl,
      GPath.drop_apply _ _ _ (Nat.zero_le _),
      GPath.drop_apply _ _ _ (by omega : n - 1 ≤ 2 * n - 1 - (n - 1)), Nat.add_zero,
      hmid.1] at h
    rw [show n - 1 + (n - 1) = 2 * n - 2 by omega] at h
    exact le_of_eq h
  have hadj : c.graph.Adj (p (2 * n - 2)) w := by
    have h := p.adj (2 * n - 2) (by omega)
    rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega, hpw] at h
    exact h
  have hdiff := hadj.diff_dist_adj (u := z)
  rw [hw] at hdiff
  have hz : c.graph.dist z (p (2 * n - 2)) = n - 1 := by
    rcases hdiff with h | h | h <;> omega
  exact ⟨hz, hz'⟩

private theorem adj_or_adj_of_delta_adj_of_height_ne (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {u v : ↥(edgeBall (n - 1) c)} (h : (delta c Good n).Adj u v)
    (hv : height c (v : c.Γ) ≠ n - 1) :
    c.graph.Adj (u : c.Γ) (v : c.Γ) ∨ c.graph.Adj (v : c.Γ) (u : c.Γ) := by
  have hrel := (delta_unfold (c := c) (Good := Good) (n := n)).mp h
  rcases hrel.2 with h' | h'
  · rcases h' with ⟨hadj, -⟩ | hB
    · exact Or.inl hadj
    · exact absurd (height_eq_of_typeB c hn hgirth hG hB).2 hv
  · rcases h' with ⟨hadj, -⟩ | hB
    · exact Or.inr hadj
    · exact absurd (height_eq_of_typeB c hn hgirth hG hB).1 hv

theorem eq_one_of_fix_of_delta (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    {z z' : c.Γ} (hz : (z = c.xv ∧ z' = c.lv) ∨ (z = c.lv ∧ z' = c.xv))
    {f : Equiv.Perm ↥(edgeBall (n - 1) c)} (hf : f ∈ deltaAut c Good n)
    (hfix : ∀ u : ↥(edgeBall (n - 1) c), c.graph.dist z (u : c.Γ) ≤ n - 1 → f u = u) :
    f = 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hc : ∀ a b, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  refine Equiv.ext fun u => ?_
  by_cases hdu : c.graph.dist z (u : c.Γ) ≤ n - 1
  · exact hfix u hdu
  · obtain ⟨hdz, hdz'⟩ := dist_eq_of_far hn hz u.2 hdu
    obtain ⟨v, hTBuv, hdv⟩ := exists_typeB_of_far hn hgirth hG hdeg hz u.2 hdu
    have hTBvu : TypeB c Good n v (u : c.Γ) := typeB_symm c hG hTBuv
    have hvmem : v ∈ edgeBall (n - 1) c :=
      (mem_edgeBall_iff hz (n - 1) v).mpr (Or.inl (le_of_eq hdv))
    let v' : ↥(edgeBall (n - 1) c) := ⟨v, hvmem⟩
    have hfv : f v' = v' := hfix v' (le_of_eq hdv)
    by_cases hdu'' : c.graph.dist z ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) ≤ n - 1
    · have h2 : f (f u) = f u := hfix (f u) hdu''
      exact f.injective h2
    · obtain ⟨hdz'', hdz'''⟩ :=
        dist_eq_of_far hn hz (f u).2 hdu''
      have hheight_u : height c (u : c.Γ) = n - 1 :=
        height_eq_of_dist_pair hz hdz hdz'
      have hheight_v : height c v = n - 1 := (height_eq_of_typeB c hn hgirth hG hTBuv).2
      have hheight_u'' : height c ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) = n - 1 :=
        height_eq_of_dist_pair hz hdz'' hdz'''
      have hux : (u : c.Γ) ≠ c.xv := by
        intro h
        rw [h] at hheight_u
        have : height c c.xv = 0 := by simp [height]
        omega
      have hul : (u : c.Γ) ≠ c.lv := by
        intro h
        rw [h] at hheight_u
        have : height c c.lv = 0 := by simp [height]
        omega
      obtain ⟨u', ⟨hu'_adj, hu'_h⟩, hu'_uniq⟩ :=
        existsUnique_adj_height_pred (c := c) (n := n) hgirth u.2 hux hul
      have hu'ball : u' ∈ edgeBall (n - 2) c :=
        mem_edgeBall_of_height_le (r := n - 2) hz (by rw [hu'_h, hheight_u]; omega)
      have hu'dist : c.graph.dist z u' ≤ n - 1 := by
        have h := dist_base_le_height_succ (r := n - 2) hz (by rw [hu'_h, hheight_u]; omega)
        omega
      have hu'mem : u' ∈ edgeBall (n - 1) c :=
        (mem_edgeBall_iff hz (n - 1) u').mpr (Or.inl hu'dist)
      have hu'fix : f ⟨u', hu'mem⟩ = ⟨u', hu'mem⟩ := hfix ⟨u', hu'mem⟩ hu'dist
      have hdel : (delta c Good n).Adj u ⟨u', hu'mem⟩ := by
        rw [delta_unfold]
        refine ⟨?_, Or.inl (Or.inl ⟨hu'_adj, Or.inr hu'ball⟩)⟩
        intro h
        have hh := congrArg (fun x : ↥(edgeBall (n - 1) c) => height c (x : c.Γ)) h
        rw [hheight_u, hu'_h] at hh
        omega
      have hdel' : (delta c Good n).Adj (f u) ⟨u', hu'mem⟩ := by
        have h := (mem_deltaAut_iff.mp hf) u ⟨u', hu'mem⟩
        rw [hu'fix] at h
        exact h.mpr hdel
      have hu'ne : height c ((⟨u', hu'mem⟩ : ↥(edgeBall (n - 1) c)) : c.Γ) ≠ n - 1 := by
        rw [hu'_h]
        omega
      have hu''adj : c.graph.Adj ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) u' ∨
          c.graph.Adj u' ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) :=
        adj_or_adj_of_delta_adj_of_height_ne hn hgirth hG hdel' hu'ne
      have hfu_not : ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) ∉ edgeBall (n - 2) c := by
        rw [mem_edgeBall_iff hz (n - 2)]
        push Not
        exact ⟨by omega, by omega⟩
      have hv_not : v ∉ edgeBall (n - 2) c := by
        have hv' : c.graph.dist z' v = n := dist_right_of_height (by omega) hz hheight_v hdv
        rw [mem_edgeBall_iff hz (n - 2)]
        push Not
        exact ⟨by omega, by omega⟩
      have hu_ne_v : (u : c.Γ) ≠ v := by
        intro h
        rw [← h, hdz] at hdv
        omega
      have hdeluv : (delta c Good n).Adj u v' := by
        rw [delta_unfold]
        exact ⟨by intro h; exact hu_ne_v (congrArg Subtype.val h), Or.inl (Or.inr hTBuv)⟩
      have hdelv : (delta c Good n).Adj v' (f u) := by
        have h := (mem_deltaAut_iff.mp hf) u v'
        rw [hfv] at h
        exact h.mpr hdeluv |>.symm
      have hTBv : TypeB c Good n v ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) := by
        have hrel := (delta_unfold (c := c) (Good := Good) (n := n)).mp hdelv
        rcases hrel.2 with h | h
        · rcases h with ⟨_, hmem⟩ | hB
          · exfalso
            rcases hmem with h' | h'
            · exact hv_not h'
            · exact hfu_not h'
          · exact hB
        · rcases h with ⟨_, hmem⟩ | hB
          · exfalso
            rcases hmem with h' | h'
            · exact hfu_not h'
            · exact hv_not h'
          · exact typeB_symm c hG hB
      obtain ⟨p, hpgood, hp0, hpv, hpmid⟩ := hTBvu
      obtain ⟨q, hqgood, hq0, hqv, hqmid⟩ := hTBv
      have hpmid' : (p (n - 1) = z ∧ p n = z') ∨ (p (n - 1) = z' ∧ p n = z) := by
        rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hpmid
        · rcases hpmid with h | h
          · exact Or.inr h
          · exact Or.inl h
      have hqmid' : (q (n - 1) = z ∧ q n = z') ∨ (q (n - 1) = z' ∧ q n = z) := by
        rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hqmid
        · rcases hqmid with h | h
          · exact Or.inr h
          · exact Or.inl h
      have hpm := typeB_middle_of_dist hn hgirth hG hz hdv hdz hpgood hp0 hpv hpmid'
      have hqm := typeB_middle_of_dist hn hgirth hG hz hdv hdz'' hqgood hq0 hqv hqmid'
      have hdist_p := dist_penultimate_of_good hn hgirth hG hdz hpgood hpv hpm
      have hdist_q := dist_penultimate_of_good hn hgirth hG hdz'' hqgood hqv hqm
      have hheight_p : height c (p (2 * n - 2)) = height c (u : c.Γ) - 1 := by
        rw [height_eq_min_dist hz hdist_p.1 hdist_p.2, hheight_u]
        omega
      have hp_height : height c (p (2 * n - 2)) = n - 2 := by
        rw [height_eq_min_dist hz hdist_p.1 hdist_p.2]
        omega
      have hq_height : height c (q (2 * n - 2)) = n - 2 := by
        rw [height_eq_min_dist hz hdist_q.1 hdist_q.2]
        omega
      have hux'' : ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) ≠ c.xv := by
        intro h
        rw [h] at hheight_u''
        have : height c c.xv = 0 := by simp [height]
        omega
      have hul'' : ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) ≠ c.lv := by
        intro h
        rw [h] at hheight_u''
        have : height c c.lv = 0 := by simp [height]
        omega
      obtain ⟨w, ⟨hw_adj, hw_h⟩, hw_uniq⟩ :=
        existsUnique_adj_height_pred (c := c) (n := n) hgirth (f u).2 hux'' hul''
      have hfu_adj_u' : c.graph.Adj ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) u' := by
        rcases hu''adj with h | h
        · exact h
        · exact h.symm
      have hu'_h'' : height c u' = height c ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) - 1 := by
        rw [hheight_u'', hu'_h]
        omega
      have hq_last : q (2 * n - 2) = u' := by
        have hq_adj : c.graph.Adj ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) (q (2 * n - 2)) := by
          have h := q.adj (2 * n - 2) (by omega)
          rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega, hqv] at h
          exact h.symm
        have hq_h : height c (q (2 * n - 2)) =
            height c ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) - 1 := by
          rw [hheight_u'', hq_height]
          omega
        exact (hw_uniq (q (2 * n - 2)) ⟨hq_adj, hq_h⟩).trans
          (hw_uniq u' ⟨hfu_adj_u', hu'_h''⟩).symm
      have hp_adj : c.graph.Adj (u : c.Γ) (p (2 * n - 2)) := by
        have h := p.adj (2 * n - 2) (by omega)
        rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega, hpv] at h
        exact h.symm
      have hp_last : p (2 * n - 2) = u' :=
        hu'_uniq (p (2 * n - 2)) ⟨hp_adj, hheight_p⟩
      have hpq : ∀ i, i ≤ n → p i = q i := by
        intro i hi
        by_cases hi' : i ≤ n - 1
        · have hgeop : (p.take (n - 1) (by omega)).IsGeodesic :=
            GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) _
              ((hG.noBack _ p hpgood).take _ _)
          have hgeoq : (q.take (n - 1) (by omega)).IsGeodesic :=
            GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) _
              ((hG.noBack _ q hqgood).take _ _)
          have heq : p.take (n - 1) (by omega) = q.take (n - 1) (by omega) :=
            hU (n - 1) _ _ hgeop hgeoq (by
              rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
                GPath.take_apply_of_le _ _ _ (Nat.zero_le _), hp0, hq0])
              (by
                rw [GPath.take_apply_of_le _ _ _ le_rfl,
                  GPath.take_apply_of_le _ _ _ le_rfl, hpm.1, hqm.1]) (by omega)
          have h := congrArg (fun r : GPath c.graph (n - 1) => r i) heq
          rwa [GPath.take_apply_of_le _ _ _ hi',
            GPath.take_apply_of_le _ _ _ hi'] at h
        · have hi'' : i = n := by omega
          subst i
          rw [hpm.2, hqm.2]
      have hpn1 : p (n + 1) = q (n + 1) := by
        have hgeop : ((p.drop n (by omega)).take (n - 2) (by omega)).IsGeodesic :=
          GPath.isGeodesic_of_noBack hconn hc hU (n - 2) (by omega) _
            (((hG.noBack _ p hpgood).drop n (by omega)).take (n - 2) (by omega))
        have hgeoq : ((q.drop n (by omega)).take (n - 2) (by omega)).IsGeodesic :=
          GPath.isGeodesic_of_noBack hconn hc hU (n - 2) (by omega) _
            (((hG.noBack _ q hqgood).drop n (by omega)).take (n - 2) (by omega))
        have heq : (p.drop n (by omega)).take (n - 2) (by omega) =
            (q.drop n (by omega)).take (n - 2) (by omega) :=
          hU (n - 2) _ _ hgeop hgeoq
            (by
              rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
                GPath.take_apply_of_le _ _ _ (Nat.zero_le _),
                GPath.drop_apply _ _ _ (Nat.zero_le _),
                GPath.drop_apply _ _ _ (Nat.zero_le _), Nat.add_zero,
                hpm.2, hqm.2])
            (by
              rw [GPath.take_apply_of_le _ _ _ le_rfl,
                GPath.take_apply_of_le _ _ _ le_rfl,
                GPath.drop_apply _ _ _ (by omega : n - 2 ≤ 2 * n - 1 - n),
                GPath.drop_apply _ _ _ (by omega : n - 2 ≤ 2 * n - 1 - n),
                show n + (n - 2) = 2 * n - 2 from by omega, hp_last, hq_last]) (by omega)
        have h := congrArg (fun r : GPath c.graph (n - 2) => r 1) heq
        rw [GPath.take_apply_of_le _ _ _ (by omega : 1 ≤ n - 2),
          GPath.take_apply_of_le _ _ _ (by omega : 1 ≤ n - 2),
          GPath.drop_apply _ _ _ (by omega : 1 ≤ 2 * n - 1 - n),
          GPath.drop_apply _ _ _ (by omega : 1 ≤ 2 * n - 1 - n)] at h
        simpa using h
      have hpq' : ∀ i, i ≤ n + 1 → p i = q i := by
        intro i hi
        by_cases hi' : i ≤ n
        · exact hpq i hi'
        · have hi'' : i = n + 1 := by omega
          subst i
          exact hpn1
      have hpt : Good (n + 1) (p.take (n + 1) (by omega)) :=
        hG.take _ _ _ _ hpgood
      obtain ⟨r, ⟨hrgood, _⟩, hruniq⟩ :=
        hG.existsUnique_extendTo (s := n + 1) (t := 2 * n - 1)
          (p.take (n + 1) (by omega)) le_rfl (by omega) hpt
      have hp_r : p = r := hruniq p
        ⟨hpgood, fun i hi => (GPath.take_apply_of_le _ _ _ hi).symm⟩
      have hq_r : q = r := hruniq q
        ⟨hqgood, fun i hi => by
          rw [GPath.take_apply_of_le _ _ _ hi]
          exact (hpq' i hi).symm⟩
      have hpaths : p = q := hp_r.trans hq_r.symm
      have hverts : (u : c.Γ) = ((f u : ↥(edgeBall (n - 1) c)) : c.Γ) := by
        rw [← hpv, ← hqv, hpaths]
      exact Subtype.ext hverts.symm

end CFSG.Quasithin.Stroth.WeissDelta

end
