module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaBasic

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

theorem height_xv : height c c.xv = 0 := by
  have h := height_eq_min_dist (c := c) (z := c.xv) (z' := c.lv) (w := c.xv)
    (Or.inl ⟨rfl, rfl⟩) (a := 0) (b := c.graph.dist c.lv c.xv)
    (SimpleGraph.dist_self) rfl
  simpa using h

theorem height_lv : height c c.lv = 0 := by
  have h := height_eq_min_dist (c := c) (z := c.lv) (z' := c.xv) (w := c.lv)
    (Or.inr ⟨rfl, rfl⟩) (a := 0) (b := c.graph.dist c.xv c.lv)
    (SimpleGraph.dist_self) rfl
  simpa using h

private theorem height_getVert_le_add (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {u v : ↥(edgeBall (n - 1) c)} (p : (delta c Good n).Walk u v) (i : ℕ) :
    height c (((p.getVert i : ↥(edgeBall (n - 1) c)) : c.Γ)) ≤ height c (u : c.Γ) + i := by
  induction i with
  | zero =>
      rw [SimpleGraph.Walk.getVert_zero]
      omega
  | succ i ih =>
      by_cases hi : i < p.length
      · have hstep := height_le_succ_of_delta_adj hn hgirth hG (p.adj_getVert_succ hi)
        omega
      · have hlt : p.length ≤ i := by omega
        have h1 : p.getVert (i + 1) = p.getVert p.length := by
          rw [SimpleGraph.Walk.getVert_of_length_le p (by omega),
            SimpleGraph.Walk.getVert_length]
        have h2 : p.getVert i = p.getVert p.length := by
          rw [SimpleGraph.Walk.getVert_of_length_le p hlt, SimpleGraph.Walk.getVert_length]
        have ih' := ih
        rw [h2] at ih'
        rw [h1]
        omega

private theorem height_getVert_le_add_rev (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {u v : ↥(edgeBall (n - 1) c)} (p : (delta c Good n).Walk u v) (i : ℕ) (hi : i ≤ p.length) :
    height c (((p.getVert i : ↥(edgeBall (n - 1) c)) : c.Γ)) ≤
      height c (v : c.Γ) + (p.length - i) := by
  have h := height_getVert_le_add hn hgirth hG p.reverse (p.length - i)
  rw [SimpleGraph.Walk.getVert_reverse] at h
  have hsub : p.length - (p.length - i) = i := Nat.sub_sub_self hi
  rw [hsub] at h
  exact h

private theorem one_le_height_of_ne {w : c.Γ} (hxv : w ≠ c.xv) (hlv : w ≠ c.lv) :
    1 ≤ height c w := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hx : 0 < c.graph.dist w c.xv := hconn.pos_dist_of_ne hxv
  have hy : 0 < c.graph.dist w c.lv := hconn.pos_dist_of_ne hlv
  have hpos : 0 < height c w := by
    simpa [height] using lt_min hx hy
  omega

private def ballGraph (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (n : ℕ) :
    SimpleGraph ↥(edgeBall (n - 1) c) :=
  SimpleGraph.fromRel fun u v => c.graph.Adj (u : c.Γ) (v : c.Γ)

private theorem ballGraph_adj_iff {u v : ↥(edgeBall (n - 1) c)} :
    (ballGraph c n).Adj u v ↔ c.graph.Adj (u : c.Γ) (v : c.Γ) := by
  rw [ballGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨fun hEq => h.ne (congrArg Subtype.val hEq), Or.inl h⟩

private def ballGraphHom (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (n : ℕ) :
    ballGraph c n →g c.graph where
  toFun u := (u : c.Γ)
  map_rel' := fun h => (ballGraph_adj_iff).mp h

private theorem walk_transfer {V : Type*} {G G' : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (h : ∀ i, i < p.length → G'.Adj (p.getVert i) (p.getVert (i + 1))) :
    ∃ q : G'.Walk u v, q.length = p.length ∧ q.support = p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl, rfl⟩
  | cons hab p ih =>
      have h0 := h 0 (by simp [SimpleGraph.Walk.length_cons])
      simp only [SimpleGraph.Walk.getVert_zero] at h0
      have h' : ∀ i, i < p.length → G'.Adj (p.getVert i) (p.getVert (i + 1)) := by
        intro i hi
        have := h (i + 1) (by simp [SimpleGraph.Walk.length_cons]; omega)
        simpa using this
      obtain ⟨q, hqlen, hqsupp⟩ := ih h'
      let q' : G'.Walk ((SimpleGraph.Walk.cons hab p).getVert 1) _ :=
        q.copy (by
          rw [SimpleGraph.Walk.getVert_cons_succ]
          exact (SimpleGraph.Walk.getVert_zero p).symm) rfl
      have hq'len : q'.length = p.length := by
        rw [show q'.length = q.length from SimpleGraph.Walk.length_copy .., hqlen]
      have hq'supp : q'.support = p.support := by
        rw [show q'.support = q.support from SimpleGraph.Walk.support_copy .., hqsupp]
      refine ⟨SimpleGraph.Walk.cons h0 q', ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons, hq'len]
      · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons, hq'supp]

private theorem isCycle_of_transfer {V : Type*} {G G' : SimpleGraph V} {u : V}
    {p : G.Walk u u} (hp : p.IsCycle) {q : G'.Walk u u} (hl : q.length = p.length)
    (hs : q.support = p.support) : q.IsCycle := by
  have hp3 : 3 ≤ p.length := hp.isCircuit.three_le_length
  have hnil : q ≠ SimpleGraph.Walk.nil := by
    intro hq
    have h0 : q.length = 0 := by simp [hq]
    omega
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, hnil, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    have he : q.edges = p.edges := by
      rw [SimpleGraph.Walk.edges_eq_zipWith_support, SimpleGraph.Walk.edges_eq_zipWith_support,
        hs]
    rw [he]
    exact hp.isTrail.edges_nodup
  · rw [hs]
    exact hp.support_nodup

private theorem le_length_of_all_typeA (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    {u : ↥(edgeBall (n - 1) c)} {w : (delta c Good n).Walk u u} (hw : w.IsCycle)
    (hA : ∀ j, j < w.length → c.graph.Adj ((w.getVert j : ↥(edgeBall (n - 1) c)) : c.Γ)
      ((w.getVert (j + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)) :
    2 * n + 2 ≤ w.length := by
  have hsteps : ∀ j, j < w.length → (ballGraph c n).Adj (w.getVert j) (w.getVert (j + 1)) :=
    fun j hj => ballGraph_adj_iff.mpr (hA j hj)
  obtain ⟨q, hqlen, hqsupp⟩ := walk_transfer (G := delta c Good n) (G' := ballGraph c n) w hsteps
  have hqcyc : q.IsCycle := isCycle_of_transfer hw hqlen hqsupp
  have hψinj : Function.Injective (ballGraphHom c n) := fun x y h => Subtype.val_injective h
  have hcyc : (q.map (ballGraphHom c n)).IsCycle := hqcyc.map hψinj
  have hle := SimpleGraph.egirth_le_length hcyc
  have hlen : (q.map (ballGraphHom c n)).length = w.length := by
    rw [SimpleGraph.Walk.length_map, hqlen]
  have hcast : ((2 * n + 2 : ℕ) : ℕ∞) ≤ ((q.map (ballGraphHom c n)).length : ℕ∞) :=
    le_trans hgirth hle
  have := ENat.natCast_le_natCast.mp hcast
  omega

private theorem two_mul_pred_le_length_of_typeB (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {a b : ↥(edgeBall (n - 1) c)} (q : (delta c Good n).Walk a b)
    (ha : height c (a : c.Γ) = 0) (hb : height c (b : c.Γ) = 0) {k : ℕ} (hk : k < q.length)
    (hB : TypeB c Good n ((q.getVert k : ↥(edgeBall (n - 1) c)) : c.Γ)
        ((q.getVert (k + 1) : ↥(edgeBall (n - 1) c)) : c.Γ) ∨
      TypeB c Good n ((q.getVert (k + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)
        ((q.getVert k : ↥(edgeBall (n - 1) c)) : c.Γ)) :
    2 * n - 1 ≤ q.length := by
  have h0 : height c (((q.getVert 0 : ↥(edgeBall (n - 1) c)) : c.Γ)) = 0 := by
    rw [SimpleGraph.Walk.getVert_zero]
    exact ha
  have hL : height c (((q.getVert q.length : ↥(edgeBall (n - 1) c)) : c.Γ)) = 0 := by
    rw [SimpleGraph.Walk.getVert_length]
    exact hb
  have hk1 : height c (((q.getVert k : ↥(edgeBall (n - 1) c)) : c.Γ)) = n - 1 := by
    rcases hB with h | h
    · exact (height_eq_of_typeB c hn hgirth hG h).1
    · exact (height_eq_of_typeB c hn hgirth hG h).2
  have hk2 : height c (((q.getVert (k + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)) = n - 1 := by
    rcases hB with h | h
    · exact (height_eq_of_typeB c hn hgirth hG h).2
    · exact (height_eq_of_typeB c hn hgirth hG h).1
  have h1 := height_getVert_le_add hn hgirth hG q k
  have h2 := height_getVert_le_add_rev hn hgirth hG q (k + 1) (by omega)
  omega

theorem le_egirth_delta (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    ((2 * n : ℕ) : ℕ∞) ≤ (delta c Good n).egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  rw [ENat.natCast_le_natCast]
  have hL3 : 3 ≤ w.length := hw.isCircuit.three_le_length
  have h0len : 0 < w.length := by omega
  have hAdj : (delta c Good n).Adj (w.getVert 0) (w.getVert 1) :=
    w.adj_getVert_succ h0len
  obtain ⟨g, hg'⟩ := exists_smul_eq_base_of_adj hn hgirth hG hdeg hAdj
  have hbase_g : c.graph.Adj ((g • (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ)
      ((g • (w.getVert 1) : ↥(edgeBall (n - 1) c)) : c.Γ) := by
    rcases hg' with hg | hg
    · have h1' : ((g • (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.xv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.1
      have h2' : ((g • (w.getVert 1) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.lv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.2
      rw [h1', h2']
      exact CosetGeom.adj_γ₀_γ₁
    · have h1' : ((g • (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.lv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.1
      have h2' : ((g • (w.getVert 1) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.xv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.2
      rw [h1', h2']
      exact CosetGeom.adj_γ₀_γ₁.symm
  have hstart_g : height c ((g • (w.getVert 1) : ↥(edgeBall (n - 1) c)) : c.Γ) = 0 := by
    rcases hg' with hg | hg
    · have h2' : ((g • (w.getVert 1) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.lv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.2
      rw [h2', height_lv]
    · have h2' : ((g • (w.getVert 1) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.xv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.2
      rw [h2', height_xv]
  have hstart0_g : height c ((g • (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) = 0 := by
    rcases hg' with hg | hg
    · have h1' : ((g • (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.xv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.1
      rw [h1', height_xv]
    · have h1' : ((g • (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) = c.lv :=
        congrArg (fun z : ↥(edgeBall (n - 1) c) => (z : c.Γ)) hg.1
      rw [h1', height_lv]
  let φ : (delta c Good n) →g (delta c Good n) :=
    { toFun := fun x => g • x
      map_rel' := fun {_ _} hxy =>
        (graphAction_deltaGroup hn hgirth hG hdeg).adj_smul g _ _ |>.mpr hxy }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h := congrArg (fun z => g⁻¹ • z) hxy
    simpa [φ] using h
  let w' : (delta c Good n).Walk (φ a) (φ a) := w.map φ
  have hw' : w'.IsCycle := hw.map hφinj
  have hw'len : w'.length = w.length := SimpleGraph.Walk.length_map φ w
  have hw'0 : w'.getVert 0 = φ (w.getVert 0) := SimpleGraph.Walk.getVert_map ..
  have hw'1 : w'.getVert 1 = φ (w.getVert 1) := SimpleGraph.Walk.getVert_map ..
  have hbase : c.graph.Adj ((w'.getVert 0 : ↥(edgeBall (n - 1) c)) : c.Γ)
      ((w'.getVert 1 : ↥(edgeBall (n - 1) c)) : c.Γ) := by
    rw [hw'0, hw'1]
    exact hbase_g
  have hstart : height c ((w'.getVert 1 : ↥(edgeBall (n - 1) c)) : c.Γ) = 0 := by
    rw [hw'1]
    exact hstart_g
  have hstart0φ : height c ((φ (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) = 0 :=
    hstart0_g
  have hφa : φ a = φ (w.getVert 0) := by rw [SimpleGraph.Walk.getVert_zero]
  have hend : height c ((φ a : ↥(edgeBall (n - 1) c)) : c.Γ) = 0 := by
    rw [show ((φ a : ↥(edgeBall (n - 1) c)) : c.Γ) =
      ((φ (w.getVert 0) : ↥(edgeBall (n - 1) c)) : c.Γ) from congrArg _ hφa]
    exact hstart0φ
  by_cases hA : ∀ j, j < w'.length → c.graph.Adj
      ((w'.getVert j : ↥(edgeBall (n - 1) c)) : c.Γ)
      ((w'.getVert (j + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)
  · have h := le_length_of_all_typeA hn hgirth hw' hA
    omega
  · push Not at hA
    obtain ⟨j, hj, hΓj⟩ := hA
    have hstep : (delta c Good n).Adj (w'.getVert j) (w'.getVert (j + 1)) :=
      w'.adj_getVert_succ hj
    rw [delta_unfold] at hstep
    obtain ⟨-, hcases⟩ := hstep
    have hB : TypeB c Good n ((w'.getVert j : ↥(edgeBall (n - 1) c)) : c.Γ)
        ((w'.getVert (j + 1) : ↥(edgeBall (n - 1) c)) : c.Γ) ∨
        TypeB c Good n ((w'.getVert (j + 1) : ↥(edgeBall (n - 1) c)) : c.Γ)
          ((w'.getVert j : ↥(edgeBall (n - 1) c)) : c.Γ) := by
      rcases hcases with (⟨h', -⟩ | h') | (⟨h', -⟩ | h')
      · exact absurd h' hΓj
      · exact Or.inl h'
      · exact absurd h'.symm hΓj
      · exact Or.inr h'
    have hj0 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exfalso
        exact hΓj hbase
      · exact hpos
    have hqlen : (w'.drop 1).length = w'.length - 1 := SimpleGraph.Walk.drop_length w' 1
    have hBq : TypeB c Good n (((w'.drop 1).getVert (j - 1) :
        ↥(edgeBall (n - 1) c)) : c.Γ)
        (((w'.drop 1).getVert (j - 1 + 1) : ↥(edgeBall (n - 1) c)) : c.Γ) ∨
        TypeB c Good n (((w'.drop 1).getVert (j - 1 + 1) :
          ↥(edgeBall (n - 1) c)) : c.Γ)
          (((w'.drop 1).getVert (j - 1) : ↥(edgeBall (n - 1) c)) : c.Γ) := by
      rw [SimpleGraph.Walk.drop_getVert, SimpleGraph.Walk.drop_getVert]
      have e1 : 1 + (j - 1) = j := by omega
      have e2 : 1 + (j - 1 + 1) = j + 1 := by omega
      rw [e1, e2]
      exact hB
    have hk : j - 1 < (w'.drop 1).length := by rw [hqlen]; omega
    have hbound := two_mul_pred_le_length_of_typeB hn hgirth hG (w'.drop 1)
      hstart hend hk hBq
    omega

private theorem vtype_ne_of_dist_eq {m : ℕ} {z z' u v : c.Γ}
    (hzz' : CosetGeom.vtype z ≠ CosetGeom.vtype z')
    (h1 : c.graph.dist u z = m) (h2 : c.graph.dist z' v = m) :
    CosetGeom.vtype u ≠ CosetGeom.vtype v := by
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hu : CosetGeom.vtype u = CosetGeom.vtype z ↔ Even m := by
    rw [← h1]
    exact GPath.dist_even_iff hconn hc u z
  have hv : CosetGeom.vtype z' = CosetGeom.vtype v ↔ Even m := by
    rw [← h2]
    exact GPath.dist_even_iff hconn hc z' v
  intro huv
  by_cases hE : Even m
  · exact hzz' ((hu.mpr hE).symm.trans (huv.trans (hv.mpr hE).symm))
  · have h1' : CosetGeom.vtype u ≠ CosetGeom.vtype z := fun h => hE (hu.mp h)
    have h2' : CosetGeom.vtype z' ≠ CosetGeom.vtype v := fun h => hE (hv.mp h)
    cases hu' : CosetGeom.vtype u <;> cases hv' : CosetGeom.vtype v <;>
      cases hz : CosetGeom.vtype z <;> cases hz' : CosetGeom.vtype z' <;> simp_all

private theorem vtype_ne_of_typeB (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {u v : c.Γ} (h : TypeB c Good n u v) :
    CosetGeom.vtype u ≠ CosetGeom.vtype v := by
  obtain ⟨p, hp, hp0, hpv, hmid⟩ := h
  have hconn : c.graph.Connected := CosetGeom.connected rfl
  have hc : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  have hU : UniqueGeod c.graph (n + 1) := uniqueGeod_succ hgirth
  have hnb : p.NoBack := hG.noBack (2 * n - 1) p hp
  have hpre : c.graph.dist (p 0) (p (n - 1)) = n - 1 := by
    have hgeo : (p.take (n - 1) (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack hconn hc hU (n - 1) (by omega) _
        (hnb.take (n - 1) (by omega))
    simpa [GPath.IsGeodesic] using hgeo
  have hpost : c.graph.dist (p n) (p (2 * n - 1)) = n - 1 := by
    have hgeo : (p.drop n (by omega)).IsGeodesic :=
      GPath.isGeodesic_of_noBack hconn hc hU (2 * n - 1 - n) (by omega) _
        (hnb.drop n (by omega))
    rw [GPath.IsGeodesic, GPath.drop_apply _ _ _ (Nat.zero_le _),
      GPath.drop_apply _ _ _ (le_rfl (a := 2 * n - 1 - n))] at hgeo
    rw [show n + (2 * n - 1 - n) = 2 * n - 1 by omega] at hgeo
    rw [show 2 * n - 1 - n = n - 1 by omega] at hgeo
    exact hgeo
  have hxy : CosetGeom.vtype c.xv ≠ CosetGeom.vtype c.lv :=
    CosetGeom.vtype_ne_of_adj CosetGeom.adj_γ₀_γ₁
  rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hdu : c.graph.dist u c.xv = n - 1 := by
      rw [← hp0, ← h1]
      exact hpre
    have hdv : c.graph.dist c.lv v = n - 1 := by
      rw [← h2, ← hpv]
      exact hpost
    exact vtype_ne_of_dist_eq hxy hdu hdv
  · have hdu : c.graph.dist u c.lv = n - 1 := by
      rw [← hp0, ← h1]
      exact hpre
    have hdv : c.graph.dist c.xv v = n - 1 := by
      rw [← h2, ← hpv]
      exact hpost
    exact vtype_ne_of_dist_eq hxy.symm hdu hdv

private theorem delta_vtype_ne (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    {u v : ↥(edgeBall (n - 1) c)} (h : (delta c Good n).Adj u v) :
    CosetGeom.vtype (u : c.Γ) ≠ CosetGeom.vtype (v : c.Γ) := by
  rw [delta_unfold] at h
  obtain ⟨-, hcases⟩ := h
  rcases hcases with (⟨hΓ, -⟩ | hB) | (⟨hΓ, -⟩ | hB)
  · exact CosetGeom.vtype_ne_of_adj hΓ
  · exact vtype_ne_of_typeB hn hgirth hG hB
  · exact (CosetGeom.vtype_ne_of_adj hΓ).symm
  · exact (vtype_ne_of_typeB hn hgirth hG hB).symm

theorem delta_bipartite (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) :
    ∃ col : ↥(edgeBall (n - 1) c) → Bool,
      ∀ a b, (delta c Good n).Adj a b → col a ≠ col b :=
  ⟨fun u => CosetGeom.vtype (u : c.Γ), fun _ _ h => delta_vtype_ne hn hgirth hG h⟩

theorem delta_adj_of_typeB (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) {u v : ↥(edgeBall (n - 1) c)}
    (h : TypeB c Good n (u : c.Γ) (v : c.Γ)) : (delta c Good n).Adj u v := by
  have hne : u ≠ v := by
    intro hEq
    exact vtype_ne_of_typeB hn hgirth hG h (congrArg (fun z : ↥(edgeBall (n - 1) c) =>
      CosetGeom.vtype (z : c.Γ)) hEq)
  rw [delta_unfold]
  exact ⟨hne, Or.inl (Or.inr h)⟩

theorem exists_delta_adj (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (u : ↥(edgeBall (n - 1) c)) : ∃ v, (delta c Good n).Adj u v := by
  by_cases hx : (u : c.Γ) = c.xv
  · have hu : u = deltaXv c n := Subtype.ext hx
    exact ⟨deltaLv c n, hu ▸ delta_adj_deltaXv_deltaLv hn⟩
  by_cases hl : (u : c.Γ) = c.lv
  · have hu : u = deltaLv c n := Subtype.ext hl
    exact ⟨deltaXv c n, hu ▸ (delta_adj_deltaXv_deltaLv hn).symm⟩
  have hh1 : 1 ≤ height c (u : c.Γ) := one_le_height_of_ne hx hl
  obtain ⟨w, ⟨huw, hwh⟩, -⟩ := existsUnique_adj_height_pred hgirth u.2 hx hl
  have hwle : height c w ≤ n - 2 := by
    have hule : height c (u : c.Γ) ≤ n - 1 := height_le_of_mem_edgeBall u.2
    omega
  have hwmem : w ∈ edgeBall (n - 1) c := mem_edgeBall_of_height_le (by omega)
  refine ⟨⟨w, hwmem⟩, ?_⟩
  exact ((delta_adj_iff_of_height_le hn hgirth hG (u := ⟨w, hwmem⟩) hwle).mpr
    huw.symm).symm

private theorem delta_dist_base_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) (w : ↥(edgeBall (n - 1) c)) :
    (delta c Good n).dist (deltaXv c n) w ≤ n - 1 ∨
      (delta c Good n).dist (deltaLv c n) w ≤ n - 1 := by
  rcases w.2 with hx | hy
  · exact Or.inl (le_trans (by simpa using dist_deltaXv_le hn hgirth hG w.2 hx) hx)
  · exact Or.inr (le_trans (by simpa using dist_deltaLv_le hn hgirth hG w.2 hy) hy)

theorem delta_dist_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (u v : ↥(edgeBall (n - 1) c)) :
    (delta c Good n).dist u v ≤ n := by
  have hconn : (delta c Good n).Connected := delta_connected hn hgirth hG
  obtain ⟨a, hua⟩ := exists_delta_adj hn hgirth hG hdeg u
  obtain ⟨g, hg'⟩ := exists_smul_eq_base_of_adj hn hgirth hG hdeg hua
  letI : GraphAction ↥(deltaGroup hn hgirth hG hdeg) (delta c Good n) :=
    graphAction_deltaGroup hn hgirth hG hdeg
  have hdist : (delta c Good n).dist (g • u) (g • v) = (delta c Good n).dist u v :=
    GPath.dist_smul hconn g u v
  have hxy : (delta c Good n).dist (deltaXv c n) (deltaLv c n) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr (delta_adj_deltaXv_deltaLv hn)
  have hyx : (delta c Good n).dist (deltaLv c n) (deltaXv c n) = 1 := by
    rw [SimpleGraph.dist_comm]
    exact hxy
  have key : (delta c Good n).dist (g • u) (g • v) ≤ n := by
    refine hg'.elim (fun hx => ?_) (fun hy => ?_)
    · have hd : (delta c Good n).dist (g • u) (g • v) =
          (delta c Good n).dist (deltaXv c n) (g • v) :=
        congrArg (fun z => (delta c Good n).dist z (g • v)) hx.1
      rw [hd]
      refine (delta_dist_base_le hn hgirth hG (g • v)).elim (fun hv => ?_) (fun hv => ?_)
      · exact le_trans hv (by omega)
      · have h := hconn.dist_triangle (u := deltaXv c n) (v := deltaLv c n) (w := g • v)
        rw [hxy] at h
        omega
    · have hd : (delta c Good n).dist (g • u) (g • v) =
          (delta c Good n).dist (deltaLv c n) (g • v) :=
        congrArg (fun z => (delta c Good n).dist z (g • v)) hy.1
      rw [hd]
      refine (delta_dist_base_le hn hgirth hG (g • v)).elim (fun hv => ?_) (fun hv => ?_)
      · have h := hconn.dist_triangle (u := deltaLv c n) (v := deltaXv c n) (w := g • v)
        rw [hyx] at h
        omega
      · exact le_trans hv (by omega)
  calc (delta c Good n).dist u v = (delta c Good n).dist (g • u) (g • v) := hdist.symm
    _ ≤ n := key

end CFSG.Quasithin.Stroth.WeissDelta

end
