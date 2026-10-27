module

public import CFSG.Milestones.ASVolI.F45.TitsLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoFacts46
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

@[expose] def burnsideF46_g2d_TwoOrb (c : α.Completion Y) (u : c.Γ) (n : ℕ) : Prop :=
  ∃ q₁ ∈ GPath.nbPaths c.graph u n, ∃ q₂ ∈ GPath.nbPaths c.graph u n,
    GPath.nbPaths c.graph u n = pathOrbit (stv c u) q₁ ∪ pathOrbit (stv c u) q₂ ∧
    Disjoint (pathOrbit (stv c u) q₁) (pathOrbit (stv c u) q₂) ∧
    Nat.card ↥(pathOrbit (stv c u) q₁) = Nat.card ↥(pathOrbit (stv c u) q₂)

section Smul

variable {c : α.Completion Y}

theorem burnsideF46_g2d_pathOrbit_smul {u : c.Γ} {n : ℕ} (q : GPath c.graph n) (g : c.G0) :
    pathOrbit (stv c (g • u)) (g • q) = (fun r => g • r) '' pathOrbit (stv c u) q := by
  ext r
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : g⁻¹ * h * g ∈ stv c u := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hh,
        inv_smul_smul]
    refine ⟨(g⁻¹ * h * g) • q, ⟨_, hh', rfl⟩, ?_⟩
    show g • ((g⁻¹ * h * g) • q) = h • g • q
    rw [← GPath.mul_smul', ← GPath.mul_smul']
    congr 1
    group
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    have hh' : g * h * g⁻¹ ∈ stv c (g • u) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
        MulAction.mem_stabilizer_iff.mp hh]
    refine ⟨g * h * g⁻¹, hh', ?_⟩
    show (g * h * g⁻¹) • g • q = g • h • q
    rw [← GPath.mul_smul', ← GPath.mul_smul']
    congr 1
    group

theorem burnsideF46_g2d_nbPaths_smul {u : c.Γ} {n : ℕ} (g : c.G0) :
    GPath.nbPaths c.graph (g • u) n = (fun r => g • r) '' GPath.nbPaths c.graph u n := by
  ext r
  constructor
  · intro hr
    refine ⟨g⁻¹ • r, ?_, ?_⟩
    · have := nbPaths_smul hr g⁻¹
      rwa [inv_smul_smul] at this
    · show g • g⁻¹ • r = r
      rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  · rintro ⟨q, hq, rfl⟩
    exact nbPaths_smul hq g

theorem burnsideF46_g2d_twoOrb_smul {u : c.Γ} {n : ℕ} (h : burnsideF46_g2d_TwoOrb c u n)
    (g : c.G0) : burnsideF46_g2d_TwoOrb c (g • u) n := by
  obtain ⟨q₁, hq₁, q₂, hq₂, hcov, hdisj, hcard⟩ := h
  have hinj : Function.Injective (fun r : GPath c.graph n => g • r) := fun r r' h => by
    have := congrArg (fun t : GPath c.graph n => g⁻¹ • t) h
    simpa [← GPath.mul_smul', GPath.one_smul'] using this
  refine ⟨g • q₁, nbPaths_smul hq₁ g, g • q₂, nbPaths_smul hq₂ g, ?_, ?_, ?_⟩
  · rw [burnsideF46_g2d_nbPaths_smul, hcov, Set.image_union, burnsideF46_g2d_pathOrbit_smul,
      burnsideF46_g2d_pathOrbit_smul]
  · rw [burnsideF46_g2d_pathOrbit_smul, burnsideF46_g2d_pathOrbit_smul]
    exact (Set.disjoint_image_iff hinj).mpr hdisj
  · rw [burnsideF46_g2d_pathOrbit_smul, burnsideF46_g2d_pathOrbit_smul,
      Nat.card_image_of_injective hinj, Nat.card_image_of_injective hinj]
    exact hcard

theorem burnsideF46_g2d_card_stabPath_smul {u : c.Γ} {n : ℕ} (k : ℕ)
    (h : ∀ q ∈ GPath.nbPaths c.graph u n, Nat.card (q.stabPath : Subgroup c.G0) = k)
    (g : c.G0) {q : GPath c.graph n} (hq : q ∈ GPath.nbPaths c.graph (g • u) n) :
    Nat.card (q.stabPath : Subgroup c.G0) = k := by
  have hq' : g⁻¹ • q ∈ GPath.nbPaths c.graph u n := by
    have := nbPaths_smul hq g⁻¹
    rwa [inv_smul_smul] at this
  have e : q = g • (g⁻¹ • q) := by rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  rw [e, GPath.stabPath_smul]
  show Nat.card ((g⁻¹ • q).stabPath.map (MulAut.conj g).toMonoidHom) = k
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h _ hq'

theorem burnsideF46_g2d_relIndex_conjSub (g : c.G0) (H K : Subgroup c.G0) :
    (conjSub g H).relIndex (conjSub g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

end Smul

structure burnsideF46_g2d_Data (c : α.Completion Y) (Qx Ql : Subgroup c.G0) : Prop where
  faithful : c.IsFaithful
  qOne : α.qOne = 2
  qTwo : α.qTwo = 2
  transX : c.PathTrans c.xv 6
  transL : c.PathTrans c.lv 5
  qn : QNormalized Qx Ql
  qx_le : Qx ≤ stv c c.xv
  ql_le : Ql ≤ stv c c.lv
  fix_x : ∀ w, c.graph.Adj c.xv w → Qx ≤ stv c w
  fix_l : ∀ w, c.graph.Adj c.lv w → Ql ≤ stv c w
  compl_l : ∀ q ∈ GPath.nbPaths c.graph c.lv 6,
    IsComplementIn q.stabPath Ql (stv c c.lv ⊓ stv c (q 1))
  idx_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 6, (q.stabPath : Subgroup c.G0) ⊓ Qx = ⊥ ∧
    (Qx ⊔ q.stabPath).relIndex (stv c c.xv ⊓ stv c (q 1)) = 2
  card_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 6, Nat.card (q.stabPath : Subgroup c.G0) = 1
  invol_x : ∀ g ∈ stv c c.xv, g * g = 1 → ∀ w, c.graph.Adj c.xv w → g • w = w
  two_orb : burnsideF46_g2d_TwoOrb c c.lv 6

namespace burnsideF46_g2d_Data

variable {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (D : burnsideF46_g2d_Data c Qx Ql)

include D

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  burnsideF4a_hval D.faithful (by rw [D.qOne]) (by rw [D.qTwo])

theorem transPt {a : c.Γ} (ha : CosetGeom.vtype a = false) : c.PathTrans a 6 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
  rw [ha] at hg
  rw [← hg, pathTrans_smul_iff]
  exact D.transX

theorem transLn {a : c.Γ} (ha : CosetGeom.vtype a = true) : c.PathTrans a 5 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
  rw [ha] at hg
  rw [← hg, pathTrans_smul_iff]
  exact D.transL

theorem Q_le (u : c.Γ) :
    c.Qvert Qx Ql u ≤ stv c u ∧ ∀ w, c.graph.Adj u w → c.Qvert Qx Ql u ≤ stv c w := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have e : c.Qvert Qx Ql u = conjSub g (cond (CosetGeom.vtype u) Ql Qx) :=
    Qvert_eq_conjSub D.qn hg
  have hbase : cond (CosetGeom.vtype u) Ql Qx ≤ stv c (c.baseVert (CosetGeom.vtype u)) ∧
      ∀ w, c.graph.Adj (c.baseVert (CosetGeom.vtype u)) w →
        cond (CosetGeom.vtype u) Ql Qx ≤ stv c w := by
    cases CosetGeom.vtype u
    · exact ⟨D.qx_le, D.fix_x⟩
    · exact ⟨D.ql_le, D.fix_l⟩
  have hs : stv c u = conjSub g (stv c (c.baseVert (CosetGeom.vtype u))) := by
    rw [← stv_smul, hg]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [e, hs]
    exact conjSub_mono g hbase.1
  · have hw' : c.graph.Adj (c.baseVert (CosetGeom.vtype u)) (g⁻¹ • w) := by
      have := (GraphAction.adj_smul g⁻¹ u w).mpr hw
      rwa [← hg, inv_smul_smul] at this
    rw [e]
    have := conjSub_mono g (hbase.2 _ hw')
    rwa [← stv_smul, smul_inv_smul] at this

theorem Q_conj (u : c.Γ) {h : c.G0} (hh : h ∈ stv c u) {x : c.G0}
    (hx : x ∈ c.Qvert Qx Ql u) : h * x * h⁻¹ ∈ c.Qvert Qx Ql u := by
  have hconj : conjSub h (c.Qvert Qx Ql u) = c.Qvert Qx Ql u := by
    rw [← Qvert_smul D.qn h u, MulAction.mem_stabilizer_iff.mp hh]
  rw [← hconj]
  exact mul_mem_conjSub hx

theorem compl_line {u : c.Γ} (hu : CosetGeom.vtype u = true) {r : GPath c.graph 6}
    (hr : r ∈ GPath.nbPaths c.graph u 6) :
    IsComplementIn r.stabPath (c.Qvert Qx Ql u) (stv c u ⊓ stv c (r 1)) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have e2 := Qvert_eq_conjSub D.qn hg
  have hg' : g • c.lv = u := by
    have := hg
    rw [hu] at this
    exact this
  have hq : g⁻¹ • r ∈ GPath.nbPaths c.graph c.lv 6 := by
    refine ⟨?_, GPath.smul_noBack hr.2⟩
    show g⁻¹ • r 0 = c.lv
    rw [hr.1, ← hg', inv_smul_smul]
  have h2 := (IsComplementIn.conjSub_iff g).mpr (D.compl_l _ hq)
  have e1 : conjSub g (g⁻¹ • r).stabPath = r.stabPath := by
    rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  have e3 : conjSub g (stv c c.lv ⊓ stv c ((g⁻¹ • r) 1)) = stv c u ⊓ stv c (r 1) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hg', GPath.smul_apply, smul_inv_smul]
  have e2' : c.Qvert Qx Ql u = conjSub g Ql := by
    rw [e2, hu]
    rfl
  rw [e1, e3, ← e2'] at h2
  exact h2

theorem idx_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {r : GPath c.graph 6}
    (hr : r ∈ GPath.nbPaths c.graph u 6) :
    (r.stabPath : Subgroup c.G0) ⊓ c.Qvert Qx Ql u = ⊥ ∧
      (c.Qvert Qx Ql u ⊔ r.stabPath).relIndex (stv c u ⊓ stv c (r 1)) = 2 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have e2 := Qvert_eq_conjSub D.qn hg
  have hg' : g • c.xv = u := by
    have := hg
    rw [hu] at this
    exact this
  have hq : g⁻¹ • r ∈ GPath.nbPaths c.graph c.xv 6 := by
    refine ⟨?_, GPath.smul_noBack hr.2⟩
    show g⁻¹ • r 0 = c.xv
    rw [hr.1, ← hg', inv_smul_smul]
  obtain ⟨h1, h2⟩ := D.idx_x _ hq
  have e1 : (r.stabPath : Subgroup c.G0) = conjSub g (g⁻¹ • r).stabPath := by
    rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  have e3 : stv c u ⊓ stv c (r 1) = conjSub g (stv c c.xv ⊓ stv c ((g⁻¹ • r) 1)) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hg', GPath.smul_apply, smul_inv_smul]
  have e2' : c.Qvert Qx Ql u = conjSub g Qx := by
    rw [e2, hu]
    rfl
  rw [e1, e3, e2', ← conjSub_inf, ← conjSub_sup, conjSub_eq_bot_iff,
    burnsideF46_g2d_relIndex_conjSub]
  exact ⟨h1, h2⟩

theorem triv_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {r : GPath c.graph 6}
    (hr : r ∈ GPath.nbPaths c.graph u 6) : (r.stabPath : Subgroup c.G0) = ⊥ := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hg
  subst hg
  exact Subgroup.eq_bot_of_card_eq _ (burnsideF46_g2d_card_stabPath_smul 1 D.card_x g hr)

theorem invol_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {g : c.G0} (hg : g ∈ stv c u)
    (hg2 : g * g = 1) {w : c.Γ} (hw : c.graph.Adj u w) : g • w = w := by
  obtain ⟨k, hk⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hk
  have hk' : k • c.xv = u := hk
  have hmem : k⁻¹ * g * k ∈ stv c c.xv := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hk', MulAction.mem_stabilizer_iff.mp hg,
      ← hk', inv_smul_smul]
  have h2 : k⁻¹ * g * k * (k⁻¹ * g * k) = 1 := by
    calc k⁻¹ * g * k * (k⁻¹ * g * k) = k⁻¹ * (g * g) * k := by group
      _ = 1 := by rw [hg2]; group
  have hw' : c.graph.Adj c.xv (k⁻¹ • w) := by
    have := (GraphAction.adj_smul k⁻¹ u w).mpr hw
    rwa [← hk', inv_smul_smul] at this
  have h := D.invol_x _ hmem h2 _ hw'
  rw [mul_smul, mul_smul, smul_inv_smul] at h
  exact smul_left_cancel _ h

theorem twoOrb_line {u : c.Γ} (hu : CosetGeom.vtype u = true) :
    burnsideF46_g2d_TwoOrb c u 6 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hg
  subst hg
  exact burnsideF46_g2d_twoOrb_smul D.two_orb g


theorem pt_F35 {a : c.Γ} (ha : CosetGeom.vtype a = false) {p : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph a 6) : GPath.F35Conclusion c.graph c.G0 a 5 p :=
  GPath.lemma_F35 (m := 5) D.hval (D.transPt ha) (connected_graph c) (hbip c) (by norm_num) hp

theorem ln_F35 {a : c.Γ} (ha : CosetGeom.vtype a = true) {p : GPath c.graph 5}
    (hp : p ∈ GPath.nbPaths c.graph a 5) : GPath.F35Conclusion c.graph c.G0 a 4 p :=
  GPath.lemma_F35 (m := 4) D.hval (D.transLn ha) (connected_graph c) (hbip c) (by norm_num) hp

theorem nb_of_geod {n : ℕ} {t : GPath c.graph n} (ht : t.IsGeodesic) :
    t ∈ GPath.nbPaths c.graph (t 0) n :=
  ⟨rfl, GPath.noBack_of_dist_eq (connected_graph c) t ht⟩

theorem uniq_of_F35 {u : c.Γ} {m : ℕ}
    (hF : ∀ p ∈ GPath.nbPaths c.graph u (m + 1), GPath.F35Conclusion c.graph c.G0 u m p)
    {i : ℕ} (hi : i < m) {s t : GPath c.graph i} (hs : s.IsGeodesic) (ht : t.IsGeodesic)
    (hs0 : s 0 = u) (ht0 : t 0 = u) (he : s i = t i) : s = t := by
  have hsnb : s ∈ GPath.nbPaths c.graph u i := by
    have := D.nb_of_geod hs
    rwa [hs0] at this
  obtain ⟨p, hp, hps⟩ := GPath.exists_extend_to D.hval (show i ≤ m + 1 by omega) hsnb
  have h := (hF p hp).2.2.2.1 i hi t ht0
    (by rw [← he, ← hps, GPath.take_apply_of_le _ _ _ le_rfl]) ht
  rw [h, hps]

theorem pt_dist {a : c.Γ} (ha : CosetGeom.vtype a = false) {i : ℕ} (hi : i ≤ 5)
    {q : GPath c.graph i} (hq : q ∈ GPath.nbPaths c.graph a i) : c.graph.dist a (q i) = i := by
  obtain ⟨p, hp⟩ := GPath.exists_nbPaths D.hval a 6
  exact (D.pt_F35 ha hp).2.1 i hi q hq

theorem ln_dist {a : c.Γ} (ha : CosetGeom.vtype a = true) {i : ℕ} (hi : i ≤ 4)
    {q : GPath c.graph i} (hq : q ∈ GPath.nbPaths c.graph a i) : c.graph.dist a (q i) = i := by
  obtain ⟨p, hp⟩ := GPath.exists_nbPaths D.hval a 5
  exact (D.ln_F35 ha hp).2.1 i hi q hq

theorem ln_dist5 {a : c.Γ} (ha : CosetGeom.vtype a = true) {q : GPath c.graph 5}
    (hq : q ∈ GPath.nbPaths c.graph a 5) : c.graph.dist a (q 5) = 5 := by
  have hb : CosetGeom.vtype (q 5) = false := by
    rw [vtype_path_odd q le_rfl (by decide), hq.1, ha]
    rfl
  have h := D.pt_dist hb le_rfl (rev_mem_nbPaths hq)
  rw [rev_apply_last, hq.1] at h
  rw [SimpleGraph.dist_comm]
  exact h

theorem uniq_ln4 {a : c.Γ} (ha : CosetGeom.vtype a = true) {s t : GPath c.graph 4}
    (hs : s.IsGeodesic) (ht : t.IsGeodesic) (hs0 : s 0 = a) (ht0 : t 0 = a) (he : s 4 = t 4) :
    s = t := by
  have hsnb : s ∈ GPath.nbPaths c.graph a 4 := by
    have := D.nb_of_geod hs
    rwa [hs0] at this
  obtain ⟨p, hp, hps⟩ := GPath.exists_extend_to D.hval (show 4 ≤ 5 by norm_num) hsnb
  rcases (D.ln_F35 ha hp).2.2.2.2.2.1 with h | ⟨hd, -⟩
  · have := (h p hp).2 t ht0 ht (by rw [← he, ← hps, GPath.take_apply_of_le _ _ _ le_rfl])
    rw [this, hps]
  · exfalso
    have h5 := D.ln_dist5 ha hp
    have := hd (p 5)
    omega

theorem pt_alt_i {u : c.Γ} (hu : CosetGeom.vtype u = false) {p : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph u 6) :
    ∀ p' ∈ GPath.nbPaths c.graph u 6, c.graph.dist u (p' 6) = 6 ∧
      ∀ q : GPath c.graph 5, q 0 = u → q.IsGeodesic → q 5 = p' 5 →
        q = p'.take 5 (by norm_num) := by
  rcases (D.pt_F35 hu hp).2.2.2.2.2.1 with h | h
  · exact h
  exfalso
  obtain ⟨-, -, huniq, -, -⟩ := h
  have hp4 : CosetGeom.vtype (p 4) = false := by
    rw [vtype_path_even p (by norm_num) (by decide), hp.1, hu]
  have hp5 : CosetGeom.vtype (p 5) = true := by
    rw [vtype_path_odd p (by norm_num) (by decide), hp.1, hu]
    rfl
  have hadj45 : c.graph.Adj (p 4) (p 5) := p.adj 4 (by norm_num)
  obtain ⟨y, hy, hy4, -⟩ := D.hval (p 5) (p 4) (p 4)
  obtain ⟨t, ⟨ht0, ht5, htg, ht4⟩, -⟩ := huniq y hy
  have ht4' : t 4 = y := ht4
  have hul : c.graph.Adj u (t 1) := by
    have := t.adj 0 (by norm_num)
    rwa [ht0] at this
  have hlt : CosetGeom.vtype (t 1) = true := by
    have := CosetGeom.vtype_ne_of_adj hul
    rw [hu] at this
    cases h : CosetGeom.vtype (t 1)
    · exact absurd h.symm this
    · rfl
  have hτg : (t.drop 1 (by norm_num)).IsGeodesic :=
    GPath.IsGeodesic.drop (connected_graph c) htg 1 (by norm_num)
  have hτ0 : (t.drop 1 (by norm_num)) 0 = t 1 := by
    rw [GPath.drop_apply _ _ _ (by norm_num)]
  have hτ4 : (t.drop 1 (by norm_num)) 4 = p 5 := by
    rw [GPath.drop_apply _ _ _ (by norm_num)]
    exact ht5
  have hτ3 : (t.drop 1 (by norm_num)) 3 = y := by
    rw [GPath.drop_apply _ _ _ (by norm_num)]
    exact ht4'
  have hpt : p.take 5 (by norm_num) ∈ GPath.nbPaths c.graph u 5 :=
    ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le 5)]; exact hp.1, hp.2.take 5 _⟩
  have hpg : (p.take 5 (by norm_num)).IsGeodesic := by
    show c.graph.dist ((p.take 5 _) 0) ((p.take 5 _) 5) = 5
    rw [hpt.1]
    exact D.pt_dist hu le_rfl hpt
  have hl1 : t 1 ≠ p 1 := by
    intro hlp
    have hσg := GPath.IsGeodesic.drop (connected_graph c) hpg 1 (by norm_num)
    have e := D.uniq_ln4 hlt hτg hσg hτ0
      (by rw [GPath.drop_apply _ _ _ (by norm_num), GPath.take_apply_of_le _ _ _ (by norm_num),
        ← hlp])
      (by rw [hτ4, GPath.drop_apply _ _ _ (by norm_num),
        GPath.take_apply_of_le _ _ _ (by norm_num)])
    have h3 := congrArg (fun r : GPath c.graph 4 => r 3) e
    rw [hτ3, GPath.drop_apply _ _ _ (by norm_num), GPath.take_apply_of_le _ _ _ (by norm_num)] at h3
    exact hy4 h3
  set s := (p.take 5 (by norm_num)).rev with hs
  have hs5 : s 5 = u := by
    rw [hs, GPath.rev_apply _ le_rfl, GPath.take_apply_of_le _ _ _ (by norm_num)]
    exact hp.1
  have hsl : c.graph.Adj (s 5) (t 1) := by rw [hs5]; exact hul
  have hs4 : s 4 = p 1 := by
    rw [hs, GPath.rev_apply _ (by norm_num), GPath.take_apply_of_le _ _ _ (by norm_num)]
  have hrnb : s.snoc (t 1) hsl ∈ GPath.nbPaths c.graph (p 5) 6 := by
    refine ⟨?_, GPath.noBack_snoc (hpt.2.rev) hsl (fun _ => ?_)⟩
    · rw [GPath.snoc_of_le _ _ _ (Nat.zero_le 5), hs, GPath.rev_apply _ (Nat.zero_le 5),
        GPath.take_apply_of_le _ _ _ le_rfl]
    · show t 1 ≠ s 4
      rw [hs4]
      exact hl1
  have hr1 : (s.snoc (t 1) hsl) 1 = p 4 := by
    rw [GPath.snoc_of_le _ _ _ (by norm_num), hs, GPath.rev_apply _ (by norm_num),
      GPath.take_apply_of_le _ _ _ (by norm_num)]
  have hcompl := D.compl_line hp5 hrnb
  have hfix : ∀ g ∈ ((s.snoc (t 1) hsl).stabPath : Subgroup c.G0), g • y = y := by
    intro g hg
    have hgl : g • t 1 = t 1 := by
      have := hg 6 le_rfl
      rwa [GPath.snoc_last] at this
    have hg5 : g • p 5 = p 5 := by
      have := hg 0 (Nat.zero_le 6)
      rwa [hrnb.1] at this
    have hgτ : (g • t.drop 1 (by norm_num)).IsGeodesic := hτg.smul (connected_graph c) g
    have e := D.uniq_ln4 hlt hgτ hτg (by rw [GPath.smul_apply, hτ0, hgl]) hτ0
      (by rw [GPath.smul_apply, hτ4, hg5])
    have h3 := congrArg (fun r : GPath c.graph 4 => r 3) e
    simp only [GPath.smul_apply] at h3
    rwa [hτ3] at h3
  obtain ⟨y', hy', hy'4, hy'y⟩ := D.hval (p 5) (p 4) y
  have e1 : burnsideF45_edge hadj45 1 = p 5 := burnsideF45_edge_one hadj45
  have e0 : burnsideF45_edge hadj45 0 = p 4 := burnsideF45_edge_zero hadj45
  obtain ⟨g, hg4, hge, hgy⟩ := GPath.exists_fix_path_smul_eq (m := 5) D.hval (D.transPt hp4)
    (i := 1) (by norm_num) (burnsideF45_edge_mem hadj45) (y := y) (y' := y')
    (by rw [e1]; exact hy) (by rw [e1]; exact hy') (fun _ => by rw [e0]; exact hy4)
    (fun _ => by rw [e0]; exact hy'4)
  have hg5 : g • p 5 = p 5 := by
    have := congrArg (fun r : GPath c.graph 1 => r 1) hge
    simpa [e1] using this
  have hgmem : g ∈ stv c (p 5) ⊓ stv c ((s.snoc (t 1) hsl) 1) :=
    ⟨MulAction.mem_stabilizer_iff.mpr hg5, by
      rw [hr1]
      exact MulAction.mem_stabilizer_iff.mpr hg4⟩
  obtain ⟨k, hk, h, hh, hkh⟩ := hcompl.2.2.2 g hgmem
  have hky : k • y' = y' := MulAction.mem_stabilizer_iff.mp ((D.Q_le (p 5)).2 y' hy' hk)
  have hhy : h • y = y' := by
    have h1 : k • (h • y) = y' := by rw [← mul_smul, hkh, hgy]
    have hk' : k⁻¹ • y' = y' := by rw [inv_smul_eq_iff, hky]
    calc h • y = k⁻¹ • (k • (h • y)) := by rw [inv_smul_smul]
      _ = k⁻¹ • y' := by rw [h1]
      _ = y' := hk'
  rw [hfix h hh] at hhy
  exact hy'y hhy.symm

theorem uniq_pt5 {u : c.Γ} (hu : CosetGeom.vtype u = false) {s t : GPath c.graph 5}
    (hs : s.IsGeodesic) (ht : t.IsGeodesic) (hs0 : s 0 = u) (ht0 : t 0 = u) (he : s 5 = t 5) :
    s = t := by
  have hsnb : s ∈ GPath.nbPaths c.graph u 5 := by
    have := D.nb_of_geod hs
    rwa [hs0] at this
  obtain ⟨p, hp, hps⟩ := GPath.exists_extend_to D.hval (show 5 ≤ 6 by norm_num) hsnb
  have h := (D.pt_alt_i hu hp p hp).2 t ht0 ht
    (by rw [← he, ← hps, GPath.take_apply_of_le _ _ _ le_rfl])
  rw [h, hps]

theorem uniqueGeod : UniqueGeod c.graph 6 := by
  intro n s t hs ht h0 hn hn6
  cases hv : CosetGeom.vtype (s 0)
  · rcases Nat.lt_or_ge n 5 with h5 | h5
    · exact D.uniq_of_F35 (fun p hp => D.pt_F35 hv hp) h5 hs ht rfl h0.symm hn
    · obtain rfl : n = 5 := by omega
      exact D.uniq_pt5 hv hs ht rfl h0.symm hn
  · rcases Nat.lt_or_ge n 4 with h4 | h4
    · exact D.uniq_of_F35 (fun p hp => D.ln_F35 hv hp) h4 hs ht rfl h0.symm hn
    · rcases Nat.lt_or_ge n 5 with h5 | h5
      · obtain rfl : n = 4 := by omega
        exact D.uniq_ln4 hv hs ht rfl h0.symm hn
      · obtain rfl : n = 5 := by omega
        have hv5 : CosetGeom.vtype (s 5) = false := by
          rw [vtype_path_odd s le_rfl (by decide), hv]
          rfl
        have e := D.uniq_pt5 hv5 hs.rev ht.rev
          (by rw [GPath.rev_apply _ (Nat.zero_le 5), Nat.sub_zero])
          (by rw [GPath.rev_apply _ (Nat.zero_le 5), Nat.sub_zero, hn])
          (by rw [rev_apply_last, rev_apply_last, h0])
        rw [← GPath.rev_rev s, e, GPath.rev_rev]

theorem uniq {n : ℕ} (hn : n < 6) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) :
    c.graph.dist a (p n) = n ∧
      ∀ q : GPath c.graph n, q 0 = a → q n = p n → q.IsGeodesic → q = p := by
  have hd : c.graph.dist a (p n) = n := by
    cases ha : CosetGeom.vtype a
    · exact D.pt_dist ha (by omega) hp
    · rcases Nat.lt_or_ge n 5 with h5 | h5
      · exact D.ln_dist ha (by omega) hp
      · obtain rfl : n = 5 := by omega
        exact D.ln_dist5 ha hp
  refine ⟨hd, fun q hq0 hqn hqg => ?_⟩
  have hpg : p.IsGeodesic := by
    show c.graph.dist (p 0) (p n) = n
    rw [hp.1]
    exact hd
  exact D.uniqueGeod n q p hqg hpg (by rw [hq0, hp.1]) hqn hn

theorem dist_m {a : c.Γ} {p : GPath c.graph 6} (hp : p ∈ GPath.nbPaths c.graph a 6) :
    c.graph.dist a (p 6) = 6 := by
  cases ha : CosetGeom.vtype a
  · exact (D.pt_alt_i ha hp p hp).1
  · have hpt : p.take 5 (by norm_num) ∈ GPath.nbPaths c.graph a 5 :=
      ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le 5)]; exact hp.1, hp.2.take 5 _⟩
    have h5 : c.graph.dist a (p 5) = 5 := by
      have := D.ln_dist5 ha hpt
      rwa [GPath.take_apply_of_le _ _ _ le_rfl] at this
    have hadj : c.graph.Adj (p 5) (p 6) := p.adj 5 (by norm_num)
    rcases GPath.dist_adj_succ_or (connected_graph c) (hbip c) a hadj with h | h
    · omega
    · exfalso
      have h4 : c.graph.dist a (p 6) = 4 := by omega
      obtain ⟨g, hg0, hg4, -⟩ := GPath.exists_geodesic' (connected_graph c) a (p 6) h4
      have hg5 : c.graph.Adj (g 4) (p 5) := by rw [hg4]; exact hadj.symm
      have hg'g : (g.snoc (p 5) hg5).IsGeodesic := by
        show c.graph.dist ((g.snoc (p 5) hg5) 0) ((g.snoc (p 5) hg5) 5) = 5
        rw [GPath.snoc_of_le _ _ _ (Nat.zero_le 4), hg0, GPath.snoc_last]
        exact h5
      have hpg : (p.take 5 (by norm_num)).IsGeodesic := by
        show c.graph.dist ((p.take 5 _) 0) ((p.take 5 _) 5) = 5
        rw [hpt.1, GPath.take_apply_of_le _ _ _ le_rfl]
        exact h5
      have e := D.uniqueGeod 5 _ _ hg'g hpg
        (by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le 4), hg0, hpt.1])
        (by rw [GPath.snoc_last, GPath.take_apply_of_le _ _ _ le_rfl]) (by norm_num)
      have h4' := congrArg (fun r : GPath c.graph 5 => r 4) e
      rw [GPath.snoc_of_le _ _ _ le_rfl, hg4, GPath.take_apply_of_le _ _ _ (by norm_num)] at h4'
      exact hp.2 4 (by norm_num) h4'.symm

theorem mem_geods {a : c.Γ} {p : GPath c.graph 6} (hp : p ∈ GPath.nbPaths c.graph a 6) :
    p ∈ c.geods 6 a (p 6) := by
  refine ⟨hp.1, rfl, ?_⟩
  show c.graph.dist (p 0) (p 6) = 6
  rw [hp.1]
  exact D.dist_m hp

theorem nbPaths_of_geods {a b : c.Γ} {t : GPath c.graph 6} (ht : t ∈ c.geods 6 a b) :
    t ∈ GPath.nbPaths c.graph a 6 :=
  ⟨ht.1, GPath.noBack_of_dist_eq (connected_graph c) t ht.2.2⟩

theorem eq_of_first {a b : c.Γ} {s t : GPath c.graph 6} (hs : s ∈ c.geods 6 a b)
    (ht : t ∈ c.geods 6 a b) (h1 : s 1 = t 1) : s = t := by
  have ds := GPath.IsGeodesic.drop (connected_graph c) hs.2.2 1 (by norm_num)
  have dt := GPath.IsGeodesic.drop (connected_graph c) ht.2.2 1 (by norm_num)
  have e : s.drop 1 (by norm_num) = t.drop 1 (by norm_num) := by
    refine D.uniqueGeod (6 - 1) _ _ ds dt ?_ ?_ (by norm_num)
    · rw [GPath.drop_apply _ _ _ (Nat.zero_le _), GPath.drop_apply _ _ _ (Nat.zero_le _)]
      exact h1
    · rw [GPath.drop_apply _ _ _ le_rfl, GPath.drop_apply _ _ _ le_rfl]
      exact hs.2.1.trans ht.2.1.symm
  exact eq_of_drop_eq (by norm_num) (hs.1.trans ht.1.symm) e

theorem stabPath_eq {a : c.Γ} {p : GPath c.graph 6} (hp : p ∈ GPath.nbPaths c.graph a 6) :
    (p.stabPath : Subgroup c.G0) = stv c a ⊓ stv c (p 1) ⊓ stv c (p 6) := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨⟨by rw [← hp.1]; exact h 0 (Nat.zero_le 6), h 1 (by norm_num)⟩, h 6 le_rfl⟩
  · rintro ⟨⟨hga, hg1⟩, hg6⟩
    have hpg := D.mem_geods hp
    have hgp : g • p ∈ c.geods 6 a (p 6) := by
      refine ⟨?_, ?_, hpg.2.2.smul (connected_graph c) g⟩
      · show g • p 0 = a
        rw [hp.1, hga]
      · show g • p 6 = p 6
        exact hg6
    have e := D.eq_of_first hgp hpg (by rw [GPath.smul_apply, hg1])
    intro i hi
    have := congrArg (fun r : GPath c.graph 6 => r i) e
    simpa using this

end burnsideF46_g2d_Data

end CFSG.ASVolI
