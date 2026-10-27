module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaGroup2
public import CFSG.Quasithin.Recognition.St84.Basic

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

theorem mem_edgeBall_of_height_le {r : ℕ} {w : c.Γ} (h : height c w ≤ r) :
    w ∈ edgeBall r c := by
  have hmin : min (c.graph.dist w c.xv) (c.graph.dist w c.lv) ≤ r := by
    simpa [height] using h
  rcases min_le_iff.mp hmin with h' | h'
  · exact Or.inl (by rw [SimpleGraph.dist_comm]; exact h')
  · exact Or.inr (by rw [SimpleGraph.dist_comm]; exact h')

private theorem height_le_succ_of_adj {u v : c.Γ} (h : c.graph.Adj u v) :
    height c v ≤ height c u + 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have h1 : c.graph.dist v c.xv ≤ c.graph.dist u c.xv + 1 := by
    have := hconn.dist_triangle (u := v) (v := u) (w := c.xv)
    rw [SimpleGraph.dist_comm (u := v) (v := u),
      SimpleGraph.dist_eq_one_iff_adj.mpr h] at this
    omega
  have h2 : c.graph.dist v c.lv ≤ c.graph.dist u c.lv + 1 := by
    have := hconn.dist_triangle (u := v) (v := u) (w := c.lv)
    rw [SimpleGraph.dist_comm (u := v) (v := u),
      SimpleGraph.dist_eq_one_iff_adj.mpr h] at this
    omega
  calc height c v = min (c.graph.dist v c.xv) (c.graph.dist v c.lv) := rfl
    _ ≤ min (c.graph.dist u c.xv + 1) (c.graph.dist u c.lv + 1) := min_le_min h1 h2
    _ = height c u + 1 := by simp only [height, min_add_add_right]

theorem height_le_succ_of_delta_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {u v : ↥(edgeBall (n - 1) c)} (h : (delta c Good n).Adj u v) :
    height c (v : c.Γ) ≤ height c (u : c.Γ) + 1 := by
  rw [delta_unfold] at h
  obtain ⟨-, hcases⟩ := h
  rcases hcases with (⟨hΓ, -⟩ | hB) | (⟨hΓ, -⟩ | hB)
  · exact height_le_succ_of_adj hΓ
  · obtain ⟨hu, hv⟩ := height_eq_of_typeB c hn hgirth hG hB
    omega
  · exact height_le_succ_of_adj hΓ.symm
  · obtain ⟨hv, hu⟩ := height_eq_of_typeB c hn hgirth hG hB
    omega

theorem delta_adj_iff_of_height_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {u v : ↥(edgeBall (n - 1) c)} (hu : height c (u : c.Γ) ≤ n - 2) :
    (delta c Good n).Adj u v ↔ c.graph.Adj u v := by
  constructor
  · intro huv
    rw [delta_unfold] at huv
    rcases huv with ⟨-, (⟨h, -⟩ | hB) | (⟨h, -⟩ | hB)⟩
    · exact h
    · exact absurd (height_eq_of_typeB c hn hgirth hG hB).1 (by omega)
    · exact h.symm
    · exact absurd (height_eq_of_typeB c hn hgirth hG hB).2 (by omega)
  · intro h
    rw [delta_unfold]
    exact ⟨fun hEq => h.ne (congrArg Subtype.val hEq),
      Or.inl (Or.inl ⟨h, Or.inl (mem_edgeBall_of_height_le hu)⟩)⟩

private theorem exists_walk_deltaXv_of_dist (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) :
    ∀ d, d ≤ n - 1 → ∀ (w : c.Γ) (hw : w ∈ edgeBall (n - 1) c),
      c.graph.dist c.xv w = d →
      ∃ q : (delta c Good n).Walk (deltaXv c n) ⟨w, hw⟩, q.length = d := by
  intro d
  induction d with
  | zero =>
      intro _ w hw hdist
      have hconn : c.graph.Connected := CosetGeom.connected rfl
      have hw' : c.xv = w := (SimpleGraph.Connected.dist_eq_zero_iff hconn).mp hdist
      have hEq : (⟨w, hw⟩ : ↥(edgeBall (n - 1) c)) = deltaXv c n := Subtype.ext hw'.symm
      rw [hEq]
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
      intro hd w hw hdist
      have hconn : c.graph.Connected := CosetGeom.connected rfl
      obtain ⟨p, hp0, hpw, -⟩ := GPath.exists_geodesic' hconn c.xv w hdist
      have hpd : c.graph.dist c.xv (p d) = d := by
        have hgeo : c.graph.dist (p 0) (p (d + 1)) = d + 1 := by
          rw [hp0, hpw, hdist]
        have h := GPath.dist_prefix hconn p hgeo (i := d) (by omega)
        rwa [hp0] at h
      have hmem : p d ∈ edgeBall (n - 1) c := Or.inl (by rw [hpd]; omega)
      have hheight : height c (p d) ≤ n - 2 := by
        have h1 : height c (p d) ≤ c.graph.dist (p d) c.xv := min_le_left _ _
        have h2 : c.graph.dist (p d) c.xv = d := by
          rw [SimpleGraph.dist_comm]
          exact hpd
        omega
      have hadj : (delta c Good n).Adj ⟨p d, hmem⟩ ⟨w, hw⟩ := by
        rw [delta_adj_iff_of_height_le hn hgirth hG hheight]
        simpa [hpw] using p.adj d (by omega)
      obtain ⟨q, hq⟩ := ih (by omega) (p d) hmem hpd
      exact ⟨q.concat hadj, by rw [SimpleGraph.Walk.length_concat, hq]⟩

private theorem exists_walk_deltaLv_of_dist (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) :
    ∀ d, d ≤ n - 1 → ∀ (w : c.Γ) (hw : w ∈ edgeBall (n - 1) c),
      c.graph.dist c.lv w = d →
      ∃ q : (delta c Good n).Walk (deltaLv c n) ⟨w, hw⟩, q.length = d := by
  intro d
  induction d with
  | zero =>
      intro _ w hw hdist
      have hconn : c.graph.Connected := CosetGeom.connected rfl
      have hw' : c.lv = w := (SimpleGraph.Connected.dist_eq_zero_iff hconn).mp hdist
      have hEq : (⟨w, hw⟩ : ↥(edgeBall (n - 1) c)) = deltaLv c n := Subtype.ext hw'.symm
      rw [hEq]
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
      intro hd w hw hdist
      have hconn : c.graph.Connected := CosetGeom.connected rfl
      obtain ⟨p, hp0, hpw, -⟩ := GPath.exists_geodesic' hconn c.lv w hdist
      have hpd : c.graph.dist c.lv (p d) = d := by
        have hgeo : c.graph.dist (p 0) (p (d + 1)) = d + 1 := by
          rw [hp0, hpw, hdist]
        have h := GPath.dist_prefix hconn p hgeo (i := d) (by omega)
        rwa [hp0] at h
      have hmem : p d ∈ edgeBall (n - 1) c := Or.inr (by rw [hpd]; omega)
      have hheight : height c (p d) ≤ n - 2 := by
        have h1 : height c (p d) ≤ c.graph.dist (p d) c.lv := min_le_right _ _
        have h2 : c.graph.dist (p d) c.lv = d := by
          rw [SimpleGraph.dist_comm]
          exact hpd
        omega
      have hadj : (delta c Good n).Adj ⟨p d, hmem⟩ ⟨w, hw⟩ := by
        rw [delta_adj_iff_of_height_le hn hgirth hG hheight]
        simpa [hpw] using p.adj d (by omega)
      obtain ⟨q, hq⟩ := ih (by omega) (p d) hmem hpd
      exact ⟨q.concat hadj, by rw [SimpleGraph.Walk.length_concat, hq]⟩

theorem dist_deltaXv_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {w : c.Γ} (hw : w ∈ edgeBall (n - 1) c)
    (hd : c.graph.dist c.xv w ≤ n - 1) :
    (delta c Good n).dist (deltaXv c n) ⟨w, hw⟩ ≤ c.graph.dist c.xv w := by
  obtain ⟨q, hq⟩ := exists_walk_deltaXv_of_dist hn hgirth hG _ hd w hw rfl
  exact hq ▸ SimpleGraph.dist_le q

theorem dist_deltaLv_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {w : c.Γ} (hw : w ∈ edgeBall (n - 1) c)
    (hd : c.graph.dist c.lv w ≤ n - 1) :
    (delta c Good n).dist (deltaLv c n) ⟨w, hw⟩ ≤ c.graph.dist c.lv w := by
  obtain ⟨q, hq⟩ := exists_walk_deltaLv_of_dist hn hgirth hG _ hd w hw rfl
  exact hq ▸ SimpleGraph.dist_le q

private theorem reachable_deltaXv_or_deltaLv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {w : c.Γ}
    (hw : w ∈ edgeBall (n - 1) c) :
    (delta c Good n).Reachable (deltaXv c n) ⟨w, hw⟩ ∨
      (delta c Good n).Reachable (deltaLv c n) ⟨w, hw⟩ := by
  rcases hw with hx | hy
  · obtain ⟨q, -⟩ := exists_walk_deltaXv_of_dist hn hgirth hG _ hx w (Or.inl hx) rfl
    exact Or.inl q.reachable
  · obtain ⟨q, -⟩ := exists_walk_deltaLv_of_dist hn hgirth hG _ hy w (Or.inr hy) rfl
    exact Or.inr q.reachable

theorem delta_connected (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) :
    (delta c Good n).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨deltaXv c n⟩⟩
  have hxy : (delta c Good n).Adj (deltaXv c n) (deltaLv c n) := delta_adj_deltaXv_deltaLv hn
  rcases reachable_deltaXv_or_deltaLv hn hgirth hG u.2 with hu | hu
  · rcases reachable_deltaXv_or_deltaLv hn hgirth hG v.2 with hv | hv
    · exact hu.symm.trans hv
    · exact hu.symm.trans ((SimpleGraph.Adj.reachable hxy).trans hv)
  · rcases reachable_deltaXv_or_deltaLv hn hgirth hG v.2 with hv | hv
    · exact hu.symm.trans ((SimpleGraph.Adj.reachable hxy.symm).trans hv)
    · exact hu.symm.trans hv

theorem exists_smul_eq_deltaXv_of_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    {a b : ↥(edgeBall (n - 1) c)}
    (ha : (delta c Good n).Adj (deltaXv c n) a)
    (hb : (delta c Good n).Adj (deltaXv c n) b) :
    ∃ g : ↥(deltaGroup hn hgirth hG hdeg),
      g • deltaXv c n = deltaXv c n ∧ g • a = b := by
  have hheight : height c ((deltaXv c n) : c.Γ) ≤ n - 2 := by
    have h0 : height c ((deltaXv c n) : c.Γ) = 0 := by simp [height, deltaXv]
    omega
  have hadja : c.graph.Adj c.xv (a : c.Γ) :=
    (delta_adj_iff_of_height_le hn hgirth hG hheight).mp ha
  have hadjb : c.graph.Adj c.xv (b : c.Γ) :=
    (delta_adj_iff_of_height_le hn hgirth hG hheight).mp hb
  obtain ⟨g, hgx, hgab⟩ := CosetGeom.exists_stab_smul_eq hadja hadjb
  let e : ↥(MulAction.stabilizer c.G0 c.xv) := ⟨g, MulAction.mem_stabilizer_iff.mpr hgx⟩
  have hdist : c.graph.dist c.xv (a : c.Γ) ≤ n - 1 := by
    have h1 : c.graph.dist c.xv (a : c.Γ) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadja
    omega
  have hact : hatX hn hgirth hG e a = b := by
    apply Subtype.ext
    rw [hatX_apply_of_dist_le hn hgirth hG (a := e) hdist]
    exact hgab
  refine ⟨⟨hatXHom hn hgirth hG hdeg e,
    Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)⟩, ?_, ?_⟩
  · simpa only [Subgroup.smul_def, Equiv.Perm.smul_def, hatXHom_apply] using
      hatX_smul_deltaXv hn hgirth hG e
  · simpa only [Subgroup.smul_def, Equiv.Perm.smul_def, hatXHom_apply] using hact

theorem exists_smul_eq_deltaLv_of_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    {a b : ↥(edgeBall (n - 1) c)}
    (ha : (delta c Good n).Adj (deltaLv c n) a)
    (hb : (delta c Good n).Adj (deltaLv c n) b) :
    ∃ g : ↥(deltaGroup hn hgirth hG hdeg),
      g • deltaLv c n = deltaLv c n ∧ g • a = b := by
  have hheight : height c ((deltaLv c n) : c.Γ) ≤ n - 2 := by
    have h0 : height c ((deltaLv c n) : c.Γ) = 0 := by simp [height, deltaLv]
    omega
  have hadja : c.graph.Adj c.lv (a : c.Γ) :=
    (delta_adj_iff_of_height_le hn hgirth hG hheight).mp ha
  have hadjb : c.graph.Adj c.lv (b : c.Γ) :=
    (delta_adj_iff_of_height_le hn hgirth hG hheight).mp hb
  obtain ⟨g, hgx, hgab⟩ := CosetGeom.exists_stab_smul_eq hadja hadjb
  let e : ↥(MulAction.stabilizer c.G0 c.lv) := ⟨g, MulAction.mem_stabilizer_iff.mpr hgx⟩
  have hdist : c.graph.dist c.lv (a : c.Γ) ≤ n - 1 := by
    have h1 : c.graph.dist c.lv (a : c.Γ) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadja
    omega
  have hact : hatY hn hgirth hG e a = b := by
    apply Subtype.ext
    rw [hatY_apply_of_dist_le hn hgirth hG (a := e) hdist]
    exact hgab
  refine ⟨⟨hatYHom hn hgirth hG hdeg e,
    Subgroup.subset_closure (Or.inr ⟨e, rfl⟩)⟩, ?_, ?_⟩
  · simpa only [Subgroup.smul_def, Equiv.Perm.smul_def, hatYHom_apply] using
      hatY_smul_deltaLv hn hgirth hG e
  · simpa only [Subgroup.smul_def, Equiv.Perm.smul_def, hatYHom_apply] using hact

theorem exists_smul_eq_base_of_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    {u v : ↥(edgeBall (n - 1) c)} (huv : (delta c Good n).Adj u v) :
    ∃ g : ↥(deltaGroup hn hgirth hG hdeg),
      (g • u = deltaXv c n ∧ g • v = deltaLv c n) ∨
        (g • u = deltaLv c n ∧ g • v = deltaXv c n) := by
  have hconn : (delta c Good n).Connected := delta_connected hn hgirth hG
  have hadj : ∀ (g : ↥(deltaGroup hn hgirth hG hdeg)) (u v : ↥(edgeBall (n - 1) c)),
      (delta c Good n).Adj (g • u) (g • v) ↔ (delta c Good n).Adj u v :=
    fun g u v => (graphAction_deltaGroup hn hgirth hG hdeg).adj_smul g u v
  have hα : ∀ a b : ↥(edgeBall (n - 1) c),
      (delta c Good n).Adj (deltaXv c n) a → (delta c Good n).Adj (deltaXv c n) b →
      ∃ h ∈ (⊤ : Subgroup ↥(deltaGroup hn hgirth hG hdeg)) ⊓
        MulAction.stabilizer ↥(deltaGroup hn hgirth hG hdeg) (deltaXv c n), h • a = b := by
    intro a b ha hb
    obtain ⟨g, hgx, hgab⟩ := exists_smul_eq_deltaXv_of_adj hn hgirth hG hdeg ha hb
    exact ⟨g, ⟨Subgroup.mem_top g, MulAction.mem_stabilizer_iff.mpr hgx⟩, hgab⟩
  have hβ : ∀ a b : ↥(edgeBall (n - 1) c),
      (delta c Good n).Adj (deltaLv c n) a → (delta c Good n).Adj (deltaLv c n) b →
      ∃ h ∈ (⊤ : Subgroup ↥(deltaGroup hn hgirth hG hdeg)) ⊓
        MulAction.stabilizer ↥(deltaGroup hn hgirth hG hdeg) (deltaLv c n), h • a = b := by
    intro a b ha hb
    obtain ⟨g, hgx, hgab⟩ := exists_smul_eq_deltaLv_of_adj hn hgirth hG hdeg ha hb
    exact ⟨g, ⟨Subgroup.mem_top g, MulAction.mem_stabilizer_iff.mpr hgx⟩, hgab⟩
  have hET := CFSG.Quasithin.St84.edgeTransitive_of_locTrans (V := ↥(edgeBall (n - 1) c))
    (G := ↥(deltaGroup hn hgirth hG hdeg)) (Γ := delta c Good n) hconn hadj
    ⊤ (delta_adj_deltaXv_deltaLv hn) hα hβ
  obtain ⟨g, -, hg | hg⟩ :=
    hET u v (deltaXv c n) (deltaLv c n) huv (delta_adj_deltaXv_deltaLv hn)
  · exact ⟨g, Or.inl hg⟩
  · exact ⟨g, Or.inr hg⟩

end CFSG.Quasithin.Stroth.WeissDelta

end
