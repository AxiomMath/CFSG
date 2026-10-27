module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Background.GirthGeodesic

public section

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

universe u v

variable {X : Type u} [Group X] {P1 P2 : Subgroup X} {Y : Type v} [Group Y]

@[expose] noncomputable def height (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (w : c.Γ) : ℕ := min (c.graph.dist w c.xv) (c.graph.dist w c.lv)

variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}

theorem dist_xv_eq_succ_or_dist_lv_eq_succ (w : c.Γ) :
    c.graph.dist w c.xv = c.graph.dist w c.lv + 1 ∨
      c.graph.dist w c.lv = c.graph.dist w c.xv + 1 :=
  GPath.dist_adj_succ_or (CosetGeom.connected rfl)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) w CosetGeom.adj_γ₀_γ₁.symm

theorem height_le_of_mem_edgeBall {n : ℕ} {w : c.Γ} (hw : w ∈ edgeBall (n - 1) c) :
    height c w ≤ n - 1 := by
  rcases hw with h | h
  · rw [SimpleGraph.dist_comm] at h
    exact le_trans (min_le_left _ _) h
  · rw [SimpleGraph.dist_comm] at h
    exact le_trans (min_le_right _ _) h

theorem existsUnique_adj_min_dist_pred {n : ℕ}
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    {a b w : c.Γ} (hdist : c.graph.dist w a = c.graph.dist w b + 1)
    (hb : c.graph.dist w b < n) (hbpos : 0 < c.graph.dist w b) :
    ∃! v, c.graph.Adj w v ∧
      min (c.graph.dist v a) (c.graph.dist v b) =
        min (c.graph.dist w a) (c.graph.dist w b) - 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hg' : ((2 * (n + 1) : ℕ) : ℕ∞) ≤ c.graph.egirth := by
    rwa [show 2 * (n + 1) = 2 * n + 2 by omega]
  have hminw : min (c.graph.dist w a) (c.graph.dist w b) = c.graph.dist w b :=
    min_eq_right (by omega)
  obtain ⟨p, hp0, hpb, -⟩ := GPath.exists_geodesic hconn w b
  have hp1 : c.graph.Adj w (p 1) := by
    have h := p.adj 0 hbpos
    rwa [hp0] at h
  have hpd : c.graph.dist (p 1) b = c.graph.dist w b - 1 := by
    have hle := GPath.dist_le_sub hconn p (i := 1) (j := c.graph.dist w b)
      (by omega) le_rfl
    rw [hpb] at hle
    have hge : c.graph.dist w b ≤ c.graph.dist w (p 1) + c.graph.dist (p 1) b :=
      hconn.dist_triangle
    have h1 : c.graph.dist w (p 1) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp1
    omega
  have hpmin : min (c.graph.dist (p 1) a) (c.graph.dist (p 1) b) =
      min (c.graph.dist w a) (c.graph.dist w b) - 1 := by
    have hpa : c.graph.dist w b ≤ c.graph.dist (p 1) a := by
      have h1 : c.graph.dist w a ≤ c.graph.dist w (p 1) + c.graph.dist (p 1) a :=
        hconn.dist_triangle
      have h2 : c.graph.dist w (p 1) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp1
      omega
    rw [hminw, hpd]
    exact min_eq_right (by omega)
  refine ⟨p 1, ⟨hp1, hpmin⟩, fun v hv => ?_⟩
  obtain ⟨hvadj, hvmin⟩ := hv
  have hva : c.graph.dist w b ≤ c.graph.dist v a := by
    have h1 : c.graph.dist w a ≤ c.graph.dist w v + c.graph.dist v a :=
      hconn.dist_triangle
    have h2 : c.graph.dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvadj
    omega
  have hvdb : c.graph.dist v b = c.graph.dist w b - 1 := by
    have hlt : ¬ c.graph.dist v a ≤ c.graph.dist v b := by
      intro hle
      have h3 : min (c.graph.dist v a) (c.graph.dist v b) = c.graph.dist v a :=
        min_eq_left hle
      rw [hvmin, hminw] at h3
      omega
    have h3 : min (c.graph.dist v a) (c.graph.dist v b) = c.graph.dist v b :=
      min_eq_right (by omega)
    rw [hvmin, hminw] at h3
    omega
  have hdu : c.graph.dist b (p 1) + 1 = c.graph.dist b w := by
    rw [SimpleGraph.dist_comm (u := b) (v := p 1), SimpleGraph.dist_comm (u := b) (v := w)]
    omega
  have hdv : c.graph.dist b v + 1 = c.graph.dist b w := by
    rw [SimpleGraph.dist_comm (u := b) (v := v), SimpleGraph.dist_comm (u := b) (v := w)]
    omega
  exact (eq_of_adj_of_dist_succ_of_le_egirth hconn hg' (y := b) (v := w)
    (by rw [SimpleGraph.dist_comm]; omega) hp1 hvadj hdu hdv).symm

theorem min_dist_eq_succ_of_adj_of_ne {n : ℕ}
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    {a b w v : c.Γ} (hab : c.graph.Adj a b)
    (hdist : c.graph.dist w a = c.graph.dist w b + 1)
    (hb : c.graph.dist w b < n) (hbpos : 0 < c.graph.dist w b)
    (hwv : c.graph.Adj w v)
    (hne : min (c.graph.dist v a) (c.graph.dist v b) ≠
      min (c.graph.dist w a) (c.graph.dist w b) - 1) :
    min (c.graph.dist v a) (c.graph.dist v b) =
      min (c.graph.dist w a) (c.graph.dist w b) + 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hg' : ((2 * (n + 1) : ℕ) : ℕ∞) ≤ c.graph.egirth := by
    rwa [show 2 * (n + 1) = 2 * n + 2 by omega]
  have hminw : min (c.graph.dist w a) (c.graph.dist w b) = c.graph.dist w b :=
    min_eq_right (by omega)
  have parityb : ∀ z z' : c.Γ, c.graph.Adj z z' → c.graph.dist z b ≠ c.graph.dist z' b := by
    intro z z' hzz' heq
    have h1 := GPath.dist_even_iff (c := CosetGeom.vtype) hconn
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) z b
    have h2 := GPath.dist_even_iff (c := CosetGeom.vtype) hconn
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) z' b
    rw [heq] at h1
    have h3 : CosetGeom.vtype z = CosetGeom.vtype b ↔
        CosetGeom.vtype z' = CosetGeom.vtype b := h1.trans h2.symm
    have h4 := CosetGeom.vtype_ne_of_adj hzz'
    cases hz : CosetGeom.vtype z <;> cases hz' : CosetGeom.vtype z' <;>
      cases hb' : CosetGeom.vtype b <;> simp_all
  have paritya : ∀ z z' : c.Γ, c.graph.Adj z z' → c.graph.dist z a ≠ c.graph.dist z' a := by
    intro z z' hzz' heq
    have h1 := GPath.dist_even_iff (c := CosetGeom.vtype) hconn
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) z a
    have h2 := GPath.dist_even_iff (c := CosetGeom.vtype) hconn
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) z' a
    rw [heq] at h1
    have h3 : CosetGeom.vtype z = CosetGeom.vtype a ↔
        CosetGeom.vtype z' = CosetGeom.vtype a := h1.trans h2.symm
    have h4 := CosetGeom.vtype_ne_of_adj hzz'
    cases hz : CosetGeom.vtype z <;> cases hz' : CosetGeom.vtype z' <;>
      cases ha' : CosetGeom.vtype a <;> simp_all
  have hvb : c.graph.dist v b = c.graph.dist w b ∨
      c.graph.dist v b = c.graph.dist w b + 1 ∨
      c.graph.dist v b = c.graph.dist w b - 1 := by
    have h := hwv.diff_dist_adj (u := b)
    rwa [SimpleGraph.dist_comm (u := b) (v := w),
      SimpleGraph.dist_comm (u := b) (v := v)] at h
  rcases hvb with h | h | h
  · exact absurd h (parityb v w hwv.symm)
  ·
    have hva : c.graph.dist v a = c.graph.dist w a ∨
        c.graph.dist v a = c.graph.dist w a + 1 ∨
        c.graph.dist v a = c.graph.dist w a - 1 := by
      have h' := hwv.diff_dist_adj (u := a)
      rwa [SimpleGraph.dist_comm (u := a) (v := w),
        SimpleGraph.dist_comm (u := a) (v := v)] at h'
    rcases hva with h' | h' | h'
    · exact absurd h' (paritya v w hwv.symm)
    · rw [hminw]
      have hm : min (c.graph.dist v a) (c.graph.dist v b) = c.graph.dist w b + 1 := by
        rw [h', h]
        omega
      rw [hm]
    ·
      exfalso
      have hva' : c.graph.dist v a = c.graph.dist w b := by omega
      have hdaw : c.graph.dist a w = c.graph.dist w b + 1 := by
        rw [SimpleGraph.dist_comm (u := a) (v := w)]
        omega
      obtain ⟨g₁, hg₁0, hg₁v, -⟩ := GPath.exists_geodesic' hconn a v
        (n := c.graph.dist w b) (by rw [SimpleGraph.dist_comm]; exact hva')
      obtain ⟨g₂, hg₂0, hg₂w, -⟩ := GPath.exists_geodesic' hconn b w
        (n := c.graph.dist w b) (by rw [SimpleGraph.dist_comm])
      let P₁ : GPath c.graph (c.graph.dist w b + 1) :=
        g₁.snoc w (by rw [hg₁v]; exact hwv.symm)
      let P₂ : GPath c.graph (c.graph.dist w b + 1) :=
        GPath.cons a g₂ (by rw [hg₂0]; exact hab)
      have hP₁0 : P₁ 0 = a := by
        simp only [P₁, GPath.snoc_of_le _ _ _ (Nat.zero_le _), hg₁0]
      have hP₁w : P₁ (c.graph.dist w b + 1) = w := by
        simp only [P₁, GPath.snoc_last]
      have hP₂0 : P₂ 0 = a := by
        simp only [P₂, GPath.cons_zero]
      have hP₂w : P₂ (c.graph.dist w b + 1) = w := by
        simp only [P₂, GPath.cons_succ, hg₂w]
      have hP₁geo : P₁.IsGeodesic := by
        show c.graph.dist (P₁ 0) (P₁ (c.graph.dist w b + 1)) = c.graph.dist w b + 1
        rw [hP₁0, hP₁w, hdaw]
      have hP₂geo : P₂.IsGeodesic := by
        show c.graph.dist (P₂ 0) (P₂ (c.graph.dist w b + 1)) = c.graph.dist w b + 1
        rw [hP₂0, hP₂w, hdaw]
      have heq := uniqueGeod_of_le_egirth hconn hg' (c.graph.dist w b + 1) P₁ P₂
        hP₁geo hP₂geo (by rw [hP₁0, hP₂0]) (by rw [hP₁w, hP₂w]) (by omega)
      have hstep : g₁ 1 = b := by
        have h1 : P₁ 1 = P₂ 1 :=
          congrArg (fun r : GPath c.graph (c.graph.dist w b + 1) => r 1) heq
        rw [show P₁ 1 = g₁ 1 from by
          simp only [P₁, GPath.snoc_of_le _ _ _ (by omega : 1 ≤ c.graph.dist w b)],
          show P₂ 1 = b from by simp only [P₂, GPath.cons_succ, hg₂0]] at h1
        exact h1
      have hle : c.graph.dist v b ≤ c.graph.dist w b - 1 := by
        have h := GPath.dist_le_sub hconn g₁ (i := 1) (j := c.graph.dist w b)
          (by omega) (le_refl _)
        rw [hstep, hg₁v] at h
        rwa [SimpleGraph.dist_comm (u := b) (v := v)] at h
      omega
  ·
    exfalso
    have hva : c.graph.dist w b ≤ c.graph.dist v a := by
      have h1 : c.graph.dist w a ≤ c.graph.dist w v + c.graph.dist v a :=
        hconn.dist_triangle
      have h2 : c.graph.dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwv
      omega
    have hm : min (c.graph.dist v a) (c.graph.dist v b) = c.graph.dist w b - 1 := by
      have h3 : min (c.graph.dist v a) (c.graph.dist v b) = c.graph.dist v b :=
        min_eq_right (by omega)
      omega
    exact hne (by rw [hm, hminw])

theorem existsUnique_adj_height_pred {n : ℕ}
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    {w : c.Γ} (hw : w ∈ edgeBall (n - 1) c) (hxv : w ≠ c.xv) (hlv : w ≠ c.lv) :
    ∃! v, c.graph.Adj w v ∧ height c v = height c w - 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hwle : height c w ≤ n - 1 := height_le_of_mem_edgeBall hw
  rcases dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) w with h | h
  ·
    have hh : height c w = c.graph.dist w c.lv := by simp [height, h]
    have hbpos : 0 < c.graph.dist w c.lv := hconn.pos_dist_of_ne hlv
    have hb : c.graph.dist w c.lv < n := by omega
    have hmain := existsUnique_adj_min_dist_pred (c := c) hgirth (a := c.xv) (b := c.lv)
      h hb hbpos
    simpa only [height, hh] using hmain
  ·
    have hh : height c w = c.graph.dist w c.xv := by simp [height, h]
    have hbpos : 0 < c.graph.dist w c.xv := hconn.pos_dist_of_ne hxv
    have hb : c.graph.dist w c.xv < n := by omega
    have hmain := existsUnique_adj_min_dist_pred (c := c) hgirth (a := c.lv) (b := c.xv)
      h hb hbpos
    simpa only [height, hh, min_comm] using hmain

theorem height_eq_succ_of_adj_of_height_ne {n : ℕ}
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    {w v : c.Γ} (hw : w ∈ edgeBall (n - 1) c) (hxv : w ≠ c.xv) (hlv : w ≠ c.lv)
    (hwv : c.graph.Adj w v) (hne : height c v ≠ height c w - 1) :
    height c v = height c w + 1 := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hwle : height c w ≤ n - 1 := height_le_of_mem_edgeBall hw
  rcases dist_xv_eq_succ_or_dist_lv_eq_succ (c := c) w with h | h
  · have hh : height c w = c.graph.dist w c.lv := by simp [height, h]
    have hbpos : 0 < c.graph.dist w c.lv := hconn.pos_dist_of_ne hlv
    have hb : c.graph.dist w c.lv < n := by omega
    have hne' : min (c.graph.dist v c.xv) (c.graph.dist v c.lv) ≠
        min (c.graph.dist w c.xv) (c.graph.dist w c.lv) - 1 := by
      simpa only [height, hh] using hne
    have hmain := min_dist_eq_succ_of_adj_of_ne (c := c) hgirth (a := c.xv) (b := c.lv)
      CosetGeom.adj_γ₀_γ₁ h hb hbpos hwv hne'
    simpa only [height, hh] using hmain
  · have hh : height c w = c.graph.dist w c.xv := by simp [height, h]
    have hbpos : 0 < c.graph.dist w c.xv := hconn.pos_dist_of_ne hxv
    have hb : c.graph.dist w c.xv < n := by omega
    have hne' : min (c.graph.dist v c.lv) (c.graph.dist v c.xv) ≠
        min (c.graph.dist w c.lv) (c.graph.dist w c.xv) - 1 := by
      simpa only [height, hh, min_comm] using hne
    have hmain := min_dist_eq_succ_of_adj_of_ne (c := c) hgirth (a := c.lv) (b := c.xv)
      CosetGeom.adj_γ₀_γ₁.symm h hb hbpos hwv hne'
    simpa only [height, hh, min_comm] using hmain

theorem height_eq_pred_or_succ_of_adj {n : ℕ}
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    {w v : c.Γ} (hw : w ∈ edgeBall (n - 1) c) (hxv : w ≠ c.xv) (hlv : w ≠ c.lv)
    (hwv : c.graph.Adj w v) :
    height c v = height c w - 1 ∨ height c v = height c w + 1 := by
  by_cases h : height c v = height c w - 1
  · exact Or.inl h
  · exact Or.inr (height_eq_succ_of_adj_of_height_ne hgirth hw hxv hlv hwv h)

theorem mem_edgeBall_of_adj_of_height_le {n : ℕ} (hn : 2 ≤ n) {w v : c.Γ}
    (hw : height c w ≤ n - 2) (hwv : c.graph.Adj w v) : v ∈ edgeBall (n - 1) c := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have h1 : c.graph.dist v c.xv ≤ c.graph.dist w c.xv + 1 := by
    have h := hconn.dist_triangle (u := v) (v := w) (w := c.xv)
    rw [SimpleGraph.dist_comm (u := v) (v := w),
      SimpleGraph.dist_eq_one_iff_adj.mpr hwv] at h
    omega
  have h2 : c.graph.dist v c.lv ≤ c.graph.dist w c.lv + 1 := by
    have h := hconn.dist_triangle (u := v) (v := w) (w := c.lv)
    rw [SimpleGraph.dist_comm (u := v) (v := w),
      SimpleGraph.dist_eq_one_iff_adj.mpr hwv] at h
    omega
  have h3 : min (c.graph.dist v c.xv) (c.graph.dist v c.lv) ≤ n - 1 := by
    have h4 : min (c.graph.dist v c.xv) (c.graph.dist v c.lv) ≤
        min (c.graph.dist w c.xv + 1) (c.graph.dist w c.lv + 1) := min_le_min h1 h2
    have h5 : min (c.graph.dist w c.xv + 1) (c.graph.dist w c.lv + 1) =
        height c w + 1 := by
      simp only [height, min_add_add_right]
    omega
  rcases min_le_iff.mp h3 with h | h
  · exact Or.inl (by rwa [SimpleGraph.dist_comm] at h)
  · exact Or.inr (by rwa [SimpleGraph.dist_comm] at h)

theorem exists_smul_eq_xv_or_lv (w : c.Γ) :
    (∃ g : c.G0, g • c.xv = w) ∨ ∃ g : c.G0, g • c.lv = w := by
  obtain ⟨g, hg⟩ := RankTwoAmalgam.Completion.exists_smul_eq_baseVert c w
  cases hv : CosetGeom.vtype w
  · exact Or.inl ⟨g, by simpa [RankTwoAmalgam.Completion.baseVert, hv] using hg⟩
  · exact Or.inr ⟨g, by simpa [RankTwoAmalgam.Completion.baseVert, hv] using hg⟩

end CFSG.Quasithin.Stroth.WeissDelta
