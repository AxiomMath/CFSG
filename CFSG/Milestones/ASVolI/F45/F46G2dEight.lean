module

public import CFSG.Milestones.ASVolI.F45.F46G2dGeo
public import CFSG.Milestones.ASVolI.F45.G2dHex
public import CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

namespace burnsideF46_g2d_Data

variable {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (D : burnsideF46_g2d_Data c Qx Ql)

include D

theorem card_nbrs [Finite α.G1] [Finite α.G2] (u : c.Γ) : Nat.card (CosetGeom.nbrs u) = 3 := by
  rw [burnsideF4b_card_nbrs D.faithful u]
  cases CosetGeom.vtype u <;> simp [RankTwoAmalgam.qv, D.qOne, D.qTwo]

theorem ncard_nbrs [Finite α.G1] [Finite α.G2] (u : c.Γ) : (c.graph.neighborSet u).ncard = 3 := by
  rw [← Nat.card_coe_set_eq]
  exact D.card_nbrs u

theorem card_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {r : GPath c.graph 6}
    (hr : r ∈ GPath.nbPaths c.graph u 6) : Nat.card (r.stabPath : Subgroup c.G0) = 1 := by
  rw [D.triv_point hu hr, Subgroup.card_bot]

theorem stab_trans_line {a : c.Γ} (ha : CosetGeom.vtype a = true) {p : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph a 6) {y y' : c.Γ} (hy : c.graph.Adj a y)
    (hy' : c.graph.Adj a y') (hy1 : y ≠ p 1) (hy'1 : y' ≠ p 1) :
    ∃ g ∈ (p.stabPath : Subgroup c.G0), g • y = y' := by
  have hp1 : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
  have hv1 : CosetGeom.vtype (p 1) = false := by
    have := CosetGeom.vtype_ne_of_adj hp1
    rw [ha] at this
    cases h : CosetGeom.vtype (p 1)
    · rfl
    · exact absurd h.symm this
  have hadj : c.graph.Adj (p 1) a := hp1.symm
  have e1 : burnsideF45_edge hadj 1 = a := burnsideF45_edge_one hadj
  have e0 : burnsideF45_edge hadj 0 = p 1 := burnsideF45_edge_zero hadj
  obtain ⟨g, hg1, hge, hgy⟩ := GPath.exists_fix_path_smul_eq (m := 5) D.hval (D.transPt hv1)
    (i := 1) (by norm_num) (burnsideF45_edge_mem hadj) (y := y) (y' := y')
    (by rw [e1]; exact hy) (by rw [e1]; exact hy') (fun _ => by rw [e0]; exact hy1)
    (fun _ => by rw [e0]; exact hy'1)
  have hga : g • a = a := by
    have := congrArg (fun r : GPath c.graph 1 => r 1) hge
    simpa [e1] using this
  obtain ⟨k, hk, h, hh, hkh⟩ := (D.compl_line ha hp).2.2.2 g
    ⟨MulAction.mem_stabilizer_iff.mpr hga, MulAction.mem_stabilizer_iff.mpr hg1⟩
  have hky : k • y' = y' := MulAction.mem_stabilizer_iff.mp ((D.Q_le a).2 y' hy' hk)
  refine ⟨h, hh, ?_⟩
  have h1 : k • (h • y) = y' := by rw [← mul_smul, hkh, hgy]
  calc h • y = k⁻¹ • (k • (h • y)) := by rw [inv_smul_smul]
    _ = k⁻¹ • y' := by rw [h1]
    _ = y' := by rw [inv_smul_eq_iff, hky]

theorem smul_geods {a b : c.Γ} {g : c.G0} (hg : g ∈ stv c a ⊓ stv c b) {t : GPath c.graph 6}
    (ht : t ∈ c.geods 6 a b) : g • t ∈ c.geods 6 a b := by
  refine ⟨?_, ?_, ht.2.2.smul (connected_graph c) g⟩
  · show g • t 0 = a
    rw [ht.1]
    exact MulAction.mem_stabilizer_iff.mp hg.1
  · show g • t 6 = b
    rw [ht.2.1]
    exact MulAction.mem_stabilizer_iff.mp hg.2

theorem trans_nbrs_line {a : c.Γ} (ha : CosetGeom.vtype a = true) {p q : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph a 6) (hq : q ∈ GPath.nbPaths c.graph a 6) (h6 : q 6 = p 6)
    (h1 : p 1 ≠ q 1) {y y' : c.Γ} (hy : c.graph.Adj a y) (hy' : c.graph.Adj a y') :
    ∃ g ∈ stv c a ⊓ stv c (p 6), g • y = y' := by
  have hp1 : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
  have hq1 : c.graph.Adj a (q 1) := burnsideF45_adj_first (by norm_num) hq
  obtain ⟨z, hz, hzp, hzq⟩ := D.hval a (p 1) (q 1)
  obtain ⟨g, hg, hgy⟩ := CFSG.Quasithin.D4Hex.sup_trans (N := c.graph.neighborSet a)
    (S₁ := (p.stabPath : Subgroup c.G0)) (S₂ := (q.stabPath : Subgroup c.G0))
    (show p 1 ∈ c.graph.neighborSet a from hp1) (show q 1 ∈ c.graph.neighborSet a from hq1)
    (show z ∈ c.graph.neighborSet a from hz) h1 hzp hzq
    (fun y hy y' hy' h₁ h₂ => D.stab_trans_line ha hp hy hy' h₁ h₂)
    (fun y hy y' hy' h₁ h₂ => D.stab_trans_line ha hq hy hy' h₁ h₂)
    (show y ∈ c.graph.neighborSet a from hy) (show y' ∈ c.graph.neighborSet a from hy')
  have hle : (p.stabPath : Subgroup c.G0) ⊔ q.stabPath ≤ stv c a ⊓ stv c (p 6) :=
    sup_le (stabPath_le_stab_ends hp.1 rfl) (stabPath_le_stab_ends hq.1 h6)
  exact ⟨g, hle hg, hgy⟩

theorem alt_line {a : c.Γ} (ha : CosetGeom.vtype a = true) {p : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph a 6) :
    (∀ t : GPath c.graph 6, t 0 = a → t 6 = p 6 → t.IsGeodesic → t = p) ∨
      BijFirst c 6 a (p 6) := by
  by_cases hu : ∀ t : GPath c.graph 6, t 0 = a → t 6 = p 6 → t.IsGeodesic → t = p
  · exact Or.inl hu
  push Not at hu
  obtain ⟨t, ht0, ht6, htg, htp⟩ := hu
  have hpg := D.mem_geods hp
  have htg' : t ∈ c.geods 6 a (p 6) := ⟨ht0, ht6, htg⟩
  have h1 : p 1 ≠ t 1 := fun h => htp (D.eq_of_first htg' hpg h.symm)
  refine Or.inr ⟨fun s hs => burnsideF45_adj_first (by norm_num) (D.nbPaths_of_geods hs),
    fun s₁ h₁ s₂ h₂ he => D.eq_of_first h₁ h₂ he, fun z hz => ?_⟩
  obtain ⟨g, hg, hgz⟩ := D.trans_nbrs_line ha hp (D.nbPaths_of_geods htg') ht6 h1
    (burnsideF45_adj_first (by norm_num) hp) hz
  exact ⟨g • p, D.smul_geods hg hpg, hgz⟩

theorem alt_point [Finite α.G1] [Finite α.G2] {a : c.Γ} (ha : CosetGeom.vtype a = false)
    {p : GPath c.graph 6} (hp : p ∈ GPath.nbPaths c.graph a 6) :
    (∀ t : GPath c.graph 6, t 0 = a → t 6 = p 6 → t.IsGeodesic → t = p) ∨
      BijFirst c 6 a (p 6) := by
  by_cases hu : ∀ t : GPath c.graph 6, t 0 = a → t 6 = p 6 → t.IsGeodesic → t = p
  · exact Or.inl hu
  push Not at hu
  obtain ⟨t, ht0, ht6, htg, htp⟩ := hu
  have hpg := D.mem_geods hp
  have htg' : t ∈ c.geods 6 a (p 6) := ⟨ht0, ht6, htg⟩
  have h1 : p 1 ≠ t 1 := fun h => htp (D.eq_of_first htg' hpg h.symm)
  refine Or.inr ⟨fun s hs => burnsideF45_adj_first (by norm_num) (D.nbPaths_of_geods hs),
    fun s₁ h₁ s₂ h₂ he => D.eq_of_first h₁ h₂ he, fun z hz => ?_⟩
  by_contra hno
  have hp1 : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
  have ht1 : c.graph.Adj a (t 1) := burnsideF45_adj_first (by norm_num) (D.nbPaths_of_geods htg')
  have hz' : c.graph.Adj a z := hz
  have hzp : z ≠ p 1 := fun h => hno ⟨p, hpg, h.symm⟩
  have hzt : z ≠ t 1 := fun h => hno ⟨t, htg', h.symm⟩
  have h3 := D.ncard_nbrs a
  obtain ⟨g, hga, hgp⟩ := D.transPt ha p t hp (D.nbPaths_of_geods htg')
  have hg6 : g • p 6 = p 6 := by
    have := congrArg (fun r : GPath c.graph 6 => r 6) hgp
    simp only [GPath.smul_apply] at this
    rw [this, ht6]
  have hgH : g ∈ stv c a ⊓ stv c (p 6) :=
    ⟨MulAction.mem_stabilizer_iff.mpr hga, MulAction.mem_stabilizer_iff.mpr hg6⟩
  have hg1 : g • p 1 = t 1 := by
    have := congrArg (fun r : GPath c.graph 6 => r 1) hgp
    simpa using this
  have hmap : ∀ w, c.graph.Adj a w → c.graph.Adj a (g • w) := fun w hw => by
    have := (GraphAction.adj_smul g a w).mpr hw
    rwa [hga] at this
  have hgz : g • z = z := by
    have hgzF : ∀ s ∈ c.geods 6 a (p 6), s 1 ≠ g • z := by
      intro s hs he
      apply hno
      refine ⟨g⁻¹ • s, D.smul_geods (inv_mem hgH) hs, ?_⟩
      show (g⁻¹ • s) 1 = z
      rw [GPath.smul_apply, he, inv_smul_smul]
    rcases burnsideF45_mem_three h3 (show p 1 ∈ c.graph.neighborSet a from hp1)
      (show t 1 ∈ c.graph.neighborSet a from ht1) (show z ∈ c.graph.neighborSet a from hz')
      h1 (Ne.symm hzp) (Ne.symm hzt) (show g • z ∈ c.graph.neighborSet a from hmap z hz') with
      e | e | e
    · exact absurd e.symm (hgzF p hpg)
    · exact absurd e.symm (hgzF t htg')
    · exact e
  have hgt : g • t 1 = p 1 := by
    rcases burnsideF45_mem_three h3 (show p 1 ∈ c.graph.neighborSet a from hp1)
      (show t 1 ∈ c.graph.neighborSet a from ht1) (show z ∈ c.graph.neighborSet a from hz')
      h1 (Ne.symm hzp) (Ne.symm hzt) (show g • t 1 ∈ c.graph.neighborSet a from hmap _ ht1) with
      e | e | e
    · exact e
    · exact absurd (smul_left_cancel g (hg1.trans e.symm)) h1
    · exact absurd (smul_left_cancel g (hgz.trans e.symm)) hzt
  have hgg : g * g ∈ (p.stabPath : Subgroup c.G0) := by
    rw [D.stabPath_eq hp]
    exact ⟨⟨MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hga, hga]),
      MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hg1, hgt])⟩,
      MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hg6, hg6])⟩
  rw [D.triv_point ha hp, Subgroup.mem_bot] at hgg
  have hfix := D.invol_point ha (MulAction.mem_stabilizer_iff.mpr hga) hgg hp1
  rw [hg1] at hfix
  exact h1 hfix.symm

theorem alt [Finite α.G1] [Finite α.G2] {a : c.Γ} {p : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph a 6) :
    (∀ t : GPath c.graph 6, t 0 = a → t 6 = p 6 → t.IsGeodesic → t = p) ∨
      BijFirst c 6 a (p 6) := by
  cases ha : CosetGeom.vtype a
  · exact D.alt_point ha hp
  · exact D.alt_line ha hp

theorem trans_nbrs_of_bij {a : c.Γ} (ha : CosetGeom.vtype a = true) {p : GPath c.graph 6}
    (hp : p ∈ GPath.nbPaths c.graph a 6) (hb : BijFirst c 6 a (p 6)) {y y' : c.Γ}
    (hy : c.graph.Adj a y) (hy' : c.graph.Adj a y') :
    ∃ h ∈ stv c a ⊓ stv c (p 6), h • y = y' := by
  obtain ⟨z, hz, hz1, -⟩ := D.hval a (p 1) (p 1)
  obtain ⟨q, hq, hq1⟩ := hb.2.2 (show z ∈ CosetGeom.nbrs a from hz)
  have hq1' : q 1 = z := hq1
  exact D.trans_nbrs_line ha hp (D.nbPaths_of_geods hq) hq.2.1
    (by rw [hq1']; exact Ne.symm hz1) hy hy'

theorem two_trans_line {a : c.Γ} (ha : CosetGeom.vtype a = true) {u₁ u₂ u₁' u₂' : c.Γ}
    (h1 : c.graph.Adj a u₁) (h2 : c.graph.Adj a u₂) (h12 : u₁ ≠ u₂) (h1' : c.graph.Adj a u₁')
    (h2' : c.graph.Adj a u₂') (h12' : u₁' ≠ u₂') :
    ∃ g ∈ stv c a, g • u₁ = u₁' ∧ g • u₂ = u₂' := by
  obtain ⟨g₁, hg₁a, hg₁u⟩ := GPath.exists_fix_smul_eq_of_dist (m := 4) D.hval (D.transLn ha)
    (connected_graph c) (k := 1) (by norm_num) (SimpleGraph.dist_eq_one_iff_adj.mpr h1)
    (SimpleGraph.dist_eq_one_iff_adj.mpr h1')
  have hv1 : CosetGeom.vtype u₁' = false := by
    have := CosetGeom.vtype_ne_of_adj h1'
    rw [ha] at this
    cases h : CosetGeom.vtype u₁'
    · rfl
    · exact absurd h.symm this
  have hadj : c.graph.Adj u₁' a := h1'.symm
  have e1 : burnsideF45_edge hadj 1 = a := burnsideF45_edge_one hadj
  have e0 : burnsideF45_edge hadj 0 = u₁' := burnsideF45_edge_zero hadj
  have hy : c.graph.Adj a (g₁ • u₂) := by
    have := (GraphAction.adj_smul g₁ a u₂).mpr h2
    rwa [hg₁a] at this
  have hy1 : g₁ • u₂ ≠ u₁' := by
    rw [← hg₁u]
    exact fun h => h12 (smul_left_cancel _ h).symm
  obtain ⟨h, hhu, hhq, hhy⟩ := GPath.exists_fix_path_smul_eq (m := 5) D.hval (D.transPt hv1)
    (i := 1) (by norm_num) (burnsideF45_edge_mem hadj) (y := g₁ • u₂) (y' := u₂')
    (by rw [e1]; exact hy) (by rw [e1]; exact h2') (fun _ => by rw [e0]; exact hy1)
    (fun _ => by rw [e0]; exact Ne.symm h12')
  have hha : h • a = a := by
    have := congrArg (fun r : GPath c.graph 1 => r 1) hhq
    simpa [e1] using this
  refine ⟨h * g₁, MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hg₁a, hha]), ?_, ?_⟩
  · rw [mul_smul, hg₁u, hhu]
  · rw [mul_smul, hhy]

theorem eight_line [Finite α.G1] [Finite α.G2] {a : c.Γ} (ha : CosetGeom.vtype a = true)
    {p : GPath c.graph 6} (hp : p ∈ GPath.nbPaths c.graph a 6) (hb : BijFirst c 6 a (p 6)) :
    IsComplementIn (stv c a ⊓ stv c (p 6)) (c.Qvert Qx Ql a) (stv c a) ∧
      (∀ q₁ ∈ c.geods 6 a (p 6), ∀ q₂ ∈ c.geods 6 a (p 6), q₁ ≠ q₂ →
        ∀ r₁ ∈ c.geods 6 a (p 6), ∀ r₂ ∈ c.geods 6 a (p 6), r₁ ≠ r₂ →
          ∃ g ∈ stv c a ⊓ stv c (p 6), g • q₁ = r₁ ∧ g • q₂ = r₂) ∧
      Nat.card ↥(c.geods 6 a (p 6)) = α.qv (CosetGeom.vtype a) + 1 := by
  have hc := D.compl_line ha hp
  have hseq := D.stabPath_eq hp
  have hcompl : IsComplementIn (stv c a ⊓ stv c (p 6)) (c.Qvert Qx Ql a) (stv c a) := by
    refine ⟨hc.1.trans inf_le_left, inf_le_left, ?_, ?_⟩
    · refine eq_bot_iff.mpr fun x hx => ?_
      have hx1 := hc.1 hx.1
      have hx2 : x ∈ p.stabPath := by
        rw [hseq]
        exact ⟨hx1, hx.2.2⟩
      have : x ∈ c.Qvert Qx Ql a ⊓ p.stabPath := ⟨hx.1, hx2⟩
      rw [hc.2.2.1] at this
      exact this
    · intro g hg
      have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hg
      have hadj : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
      have hadj' : c.graph.Adj a (g • p 1) := by
        have := (GraphAction.adj_smul g a (p 1)).mpr hadj
        rwa [hga] at this
      obtain ⟨h, hh, hhy⟩ := D.trans_nbrs_of_bij ha hp hb hadj hadj'
      have hha : h • a = a := MulAction.mem_stabilizer_iff.mp hh.1
      have hmem : h⁻¹ * g ∈ stv c a ⊓ stv c (p 1) := by
        refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
        · rw [mul_smul, hga, inv_smul_eq_iff]
          exact hha.symm
        · rw [mul_smul, ← hhy, inv_smul_smul]
      obtain ⟨q, hq, k, hk, hqk⟩ := hc.2.2.2 _ hmem
      have hkab : k ∈ stv c a ⊓ stv c (p 6) := by
        rw [hseq] at hk
        exact ⟨hk.1.1, hk.2⟩
      refine ⟨h * q * h⁻¹, D.Q_conj a hh.1 hq, h * k,
        (stv c a ⊓ stv c (p 6)).mul_mem hh hkab, ?_⟩
      calc h * q * h⁻¹ * (h * k) = h * (q * k) := by group
        _ = g := by rw [hqk]; group
  refine ⟨hcompl, ?_, ?_⟩
  · intro q₁ hq₁ q₂ hq₂ hne r₁ hr₁ r₂ hr₂ hne'
    have i1 : q₁ 1 ≠ q₂ 1 := fun h => hne (hb.2.1 hq₁ hq₂ h)
    have i2 : r₁ 1 ≠ r₂ 1 := fun h => hne' (hb.2.1 hr₁ hr₂ h)
    obtain ⟨g, hg, hg1, hg2⟩ := D.two_trans_line ha (hb.1 hq₁) (hb.1 hq₂) i1 (hb.1 hr₁)
      (hb.1 hr₂) i2
    obtain ⟨x, hx, h, hh, hxh⟩ := hcompl.2.2.2 g hg
    have hxfix : ∀ w, c.graph.Adj a w → x⁻¹ • w = w := fun w hw =>
      MulAction.mem_stabilizer_iff.mp ((D.Q_le a).2 w hw (inv_mem hx))
    have hh' : h = x⁻¹ * g := by
      rw [← hxh]
      group
    have e1 : h • q₁ 1 = r₁ 1 := by
      rw [hh', mul_smul, hg1, hxfix _ (hb.1 hr₁)]
    have e2 : h • q₂ 1 = r₂ 1 := by
      rw [hh', mul_smul, hg2, hxfix _ (hb.1 hr₂)]
    exact ⟨h, hh, hb.2.1 (D.smul_geods hh hq₁) hr₁ (by simpa using e1),
      hb.2.1 (D.smul_geods hh hq₂) hr₂ (by simpa using e2)⟩
  · rw [Nat.card_congr (hb.equiv _), burnsideF4b_card_nbrs D.faithful a]

theorem trans_geods_point {a : c.Γ} (ha : CosetGeom.vtype a = false) {b : c.Γ}
    {q₁ q₂ : GPath c.graph 6} (h₁ : q₁ ∈ c.geods 6 a b) (h₂ : q₂ ∈ c.geods 6 a b) :
    ∃ g ∈ stv c a ⊓ stv c b, g • q₁ = q₂ := by
  obtain ⟨g, hga, hgq⟩ := D.transPt ha q₁ q₂ (D.nbPaths_of_geods h₁) (D.nbPaths_of_geods h₂)
  refine ⟨g, ⟨MulAction.mem_stabilizer_iff.mpr hga, MulAction.mem_stabilizer_iff.mpr ?_⟩, hgq⟩
  have := congrArg (fun r : GPath c.graph 6 => r 6) hgq
  simp only [GPath.smul_apply] at this
  calc g • b = g • q₁ 6 := by rw [h₁.2.1]
    _ = q₂ 6 := this
    _ = b := h₂.2.1

theorem eight_point [Finite α.G1] [Finite α.G2] {a : c.Γ} (ha : CosetGeom.vtype a = false)
    {p : GPath c.graph 6} (hp : p ∈ GPath.nbPaths c.graph a 6) (hb : BijFirst c 6 a (p 6)) :
    Nonempty (↥(stv c a ⊓ stv c (p 6)) ≃* Multiplicative (ZMod 3)) ∧
      (∀ q₁ ∈ c.geods 6 a (p 6), ∀ q₂ ∈ c.geods 6 a (p 6),
        ∃ g ∈ stv c a ⊓ stv c (p 6), g • q₁ = q₂) ∧
      Nat.card ↥(c.geods 6 a (p 6)) = 3 := by
  refine ⟨?_, fun q₁ h₁ q₂ h₂ => D.trans_geods_point ha h₁ h₂, ?_⟩
  · have hseq := D.stabPath_eq hp
    have hadj : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
    have hst : stv c (p 1) ⊓ (stv c a ⊓ stv c (p 6)) = p.stabPath := by
      rw [hseq]
      ext g
      simp only [Subgroup.mem_inf]
      tauto
    have horb : MulAction.orbit ↥(stv c a ⊓ stv c (p 6)) (p 1) = CosetGeom.nbrs a := by
      ext t
      constructor
      · rintro ⟨g, rfl⟩
        have hga : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2.1
        show c.graph.Adj a ((g : c.G0) • p 1)
        have := (GraphAction.adj_smul (g : c.G0) a (p 1)).mpr hadj
        rwa [hga] at this
      · intro ht
        obtain ⟨q, hq, hq1⟩ := hb.2.2 ht
        obtain ⟨g, hg, hgq⟩ := D.trans_geods_point ha (D.mem_geods hp) hq
        refine ⟨⟨g, hg⟩, ?_⟩
        show g • p 1 = t
        rw [← GPath.smul_apply, hgq]
        exact hq1
    have hcard : Nat.card ↥(stv c a ⊓ stv c (p 6)) = 3 := by
      have h1 := Subgroup.relIndex_mul_card (stv c (p 1)) (stv c a ⊓ stv c (p 6))
      rw [hst, D.card_point ha hp, burnsideF45_relIndex_stv, horb, ← Nat.card_coe_set_eq,
        D.card_nbrs a] at h1
      omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic ↥(stv c a ⊓ stv c (p 6)) := isCyclic_of_prime_card hcard
    exact ⟨mulEquivOfCyclicCardEq (by rw [hcard]; simp)⟩
  · rw [Nat.card_congr (hb.equiv _), D.card_nbrs a]

theorem paths_trans [Finite α.G1] [Finite α.G2] {a : c.Γ} {q₁ q₂ : GPath c.graph 6}
    (h₁ : q₁ ∈ GPath.nbPaths c.graph a 6) (h₂ : q₂ ∈ GPath.nbPaths c.graph a 6)
    (he : q₁ 6 = q₂ 6) : ∃ g ∈ stv c a ⊓ stv c (q₁ 6), g • q₁ = q₂ := by
  have hg₂ : q₂ ∈ c.geods 6 a (q₁ 6) := by
    have := D.mem_geods h₂
    rwa [← he] at this
  cases ha : CosetGeom.vtype a
  · exact D.trans_geods_point ha (D.mem_geods h₁) hg₂
  · rcases D.alt_line ha h₁ with hi | hb
    · refine ⟨1, one_mem _, ?_⟩
      rw [GPath.one_smul']
      exact (hi q₂ h₂.1 he.symm hg₂.2.2).symm
    · obtain ⟨g, hg, hg1⟩ := D.trans_nbrs_of_bij ha h₁ hb (hb.1 (D.mem_geods h₁)) (hb.1 hg₂)
      exact ⟨g, hg, hb.2.1 (D.smul_geods hg (D.mem_geods h₁)) hg₂ (by simpa using hg1)⟩

theorem five (a : c.Γ) {q : GPath c.graph 6} (hq : q ∈ GPath.nbPaths c.graph a 6) :
    IsComplementIn (q.stabPath : Subgroup c.G0) (c.Qvert Qx Ql (q 6)) (stv c (q 5) ⊓ stv c (q 6)) ∨
      (CosetGeom.vtype a = false ∧ (q.stabPath : Subgroup c.G0) ⊓ c.Qvert Qx Ql (q 6) = ⊥ ∧
        (c.Qvert Qx Ql (q 6) ⊔ (q.stabPath : Subgroup c.G0)).relIndex
          (stv c (q 5) ⊓ stv c (q 6)) = 2) := by
  have hrev : q.rev ∈ GPath.nbPaths c.graph (q 6) 6 := rev_mem_nbPaths hq
  have hv : CosetGeom.vtype (q 6) = CosetGeom.vtype a := by
    rw [vtype_path_even q le_rfl (by decide), hq.1]
  have e1 : q.rev 1 = q 5 := by rw [GPath.rev_apply _ (by norm_num)]
  have es : (q.rev.stabPath : Subgroup c.G0) = q.stabPath := GPath.stabPath_rev q
  cases ha : CosetGeom.vtype a
  · right
    have h := D.idx_point (by rw [hv, ha]) hrev
    rw [es, e1, inf_comm (stv c (q 6))] at h
    exact ⟨rfl, h⟩
  · left
    have h := D.compl_line (by rw [hv, ha]) hrev
    rw [es, e1, inf_comm] at h
    exact h

theorem trans_sphere {n : ℕ} (hn : n < 6) (a : c.Γ) {v w : c.Γ} (hv : c.graph.dist a v = n)
    (hw : c.graph.dist a w = n) : ∃ g : c.G0, g • a = a ∧ g • v = w := by
  cases ha : CosetGeom.vtype a
  · exact GPath.exists_fix_smul_eq_of_dist (m := 5) D.hval (D.transPt ha) (connected_graph c)
      (by omega) hv hw
  · exact GPath.exists_fix_smul_eq_of_dist (m := 4) D.hval (D.transLn ha) (connected_graph c)
      (by omega) hv hw

theorem mem_stabPath_iff_fix {n : ℕ} (hn : n < 6) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) {g : c.G0} (hga : g • a = a) :
    g ∈ p.stabPath ↔ g • p n = p n := by
  constructor
  · intro h
    exact h n le_rfl
  · intro h
    have hpg : g • p ∈ GPath.nbPaths c.graph a n := by
      refine ⟨?_, GPath.smul_noBack hp.2⟩
      show g • p 0 = a
      rw [hp.1, hga]
    have hgeo : (g • p).IsGeodesic := by
      show c.graph.dist ((g • p) 0) ((g • p) n) = n
      rw [hpg.1]
      exact (D.uniq hn hpg).1
    have := (D.uniq hn hp).2 (g • p) hpg.1 (by simpa using h) hgeo
    intro i hi
    have := congrArg (fun r : GPath c.graph n => r i) this
    simpa using this

theorem no_polygon {n : ℕ} (hn2 : 2 ≤ n) (hn : n < 6) (S : Set c.Γ) :
    ¬ IsPolygon c.graph S (2 * n) := by
  rintro ⟨φ⟩
  have hM : 0 < 2 * n := by omega
  have hM3 : 3 ≤ 2 * n := by omega
  have := GPath.two_mul_le_of_periodic (c := CosetGeom.vtype) (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) D.uniqueGeod (GPath.polyWalk hM φ 0)
    (GPath.polyWalk_adj hM φ 0 hM3) (GPath.polyWalk_nb hM φ 0 hM3) hM (GPath.polyWalk_per hM φ 0)
  omega

theorem six {n : ℕ} (hn : n < 6) {a : c.Γ} {q : GPath c.graph n}
    (hq : q ∈ GPath.nbPaths c.graph a n) :
    (∀ u ∈ CosetGeom.sphere n a, ∀ v ∈ CosetGeom.sphere n a, ∃ g ∈ stv c a, g • u = v) ∧
      q n ∈ CosetGeom.sphere n a ∧ q.IsGeodesic ∧
      (∀ r : GPath c.graph n, r 0 = a → r n = q n → r.IsGeodesic → r = q) ∧
      (2 ≤ n → ∀ S : Set c.Γ, ¬ IsPolygon c.graph S (2 * n)) ∧
      Nat.card ↥(CosetGeom.sphere n a) = (q.stabPath : Subgroup c.G0).relIndex (stv c a) := by
  have hu := D.uniq hn hq
  have hv : q n ∈ CosetGeom.sphere n a := hu.1
  refine ⟨fun u hu' v hv' => ?_, hv, ?_, hu.2, fun h2 S => D.no_polygon h2 hn S, ?_⟩
  · obtain ⟨g, hga, hgv⟩ := D.trans_sphere hn a hu' hv'
    exact ⟨g, MulAction.mem_stabilizer_iff.mpr hga, hgv⟩
  · show c.graph.dist (q 0) (q n) = n
    rw [hq.1]
    exact hu.1
  · have horb : MulAction.orbit (stv c a) (q n) = CosetGeom.sphere n a := by
      ext w
      constructor
      · rintro ⟨g, rfl⟩
        have hg : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2
        show c.graph.dist a ((g : c.G0) • q n) = n
        have := GPath.dist_smul (connected_graph c) (g : c.G0) a (q n)
        rw [hg] at this
        rw [this]
        exact hv
      · intro hw
        obtain ⟨g, hga, hgv⟩ := D.trans_sphere hn a hv hw
        exact ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hga⟩, hgv⟩
    have hstab : MulAction.stabilizer (stv c a) (q n) = q.stabPath.subgroupOf (stv c a) := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have hg : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2
      rw [D.mem_stabPath_iff_fix hn hq hg]
      rfl
    rw [← horb, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (stv c a) (q n)), hstab]
    rfl

theorem four [Finite α.G1] [Finite α.G2] {n : ℕ} (hn : n ≤ 6) {a : c.Γ}
    (hex : ¬ (CosetGeom.vtype a = true ∧ n = 6)) {q : GPath c.graph n}
    (hq : q ∈ GPath.nbPaths c.graph a n) :
    (q.stabPath : Subgroup c.G0).relIndex (stv c a) = α.pathNum (CosetGeom.vtype a) n := by
  cases ha : CosetGeom.vtype a
  · have := burnsideF4b_relIndex_pathNum D.faithful D.hval (m := 5) (D.transPt ha) n hn q hq
    rwa [ha] at this
  · have hn5 : n ≤ 5 := by
      by_contra h
      exact hex ⟨ha, by omega⟩
    have := burnsideF4b_relIndex_pathNum D.faithful D.hval (m := 4) (D.transLn ha) n hn5 q hq
    rwa [ha] at this

end burnsideF46_g2d_Data

end CFSG.ASVolI
