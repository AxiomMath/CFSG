module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Milestones.ASVolI.F1
public import CFSG.Milestones.ASVolI.F45.TitsLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexBase

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}

theorem burnsideF46_g2d_point_card_of (hpoly : IsGenPolygon c.graph 6)
    (htrans : c.PathTrans c.xv 6) (hn3 : Nat.card ↥(CosetGeom.nbrs c.xv) = 3)
    (h9 : ∀ v, c.graph.dist c.xv v = 6 →
      Nat.card ↥(stv c c.xv ⊓ stv c v) = 10 ∨ Nat.card ↥(stv c c.xv ⊓ stv c v) = 3)
    {q : GPath c.graph 6} (hq : q ∈ GPath.nbPaths c.graph c.xv 6) :
    Nat.card (q.stabPath : Subgroup c.G0) = 1 := by
  have hv : c.graph.dist c.xv (q 6) = 6 := CFSG.Quasithin.D4Hex.end_dist hpoly le_rfl hq
  have hq1 : c.graph.Adj c.xv (q 1) := burnsideF45_adj_first (by norm_num) hq
  have horb : MulAction.orbit ↥(stv c c.xv ⊓ stv c (q 6)) (q 1) = CosetGeom.nbrs c.xv := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      have hgx : (g : c.G0) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp g.2.1
      show c.graph.Adj c.xv ((g : c.G0) • q 1)
      have := (GraphAction.adj_smul (g : c.G0) c.xv (q 1)).mpr hq1
      rwa [hgx] at this
    · intro hw
      obtain ⟨r, hr, hr1, hr6⟩ := CFSG.Quasithin.D4Hex.exists_base_path hpoly hw hv
      obtain ⟨g, hgx, hgr⟩ := htrans q r hq hr
      have hg6 : g • q 6 = q 6 := by
        have := congrArg (fun t : GPath c.graph 6 => t 6) hgr
        simp only [GPath.smul_apply] at this
        rw [this, hr6]
      refine ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hgx, MulAction.mem_stabilizer_iff.mpr hg6⟩, ?_⟩
      show g • q 1 = w
      have := congrArg (fun t : GPath c.graph 6 => t 1) hgr
      simp only [GPath.smul_apply] at this
      rw [this, hr1]
  have hst : stv c (q 1) ⊓ (stv c c.xv ⊓ stv c (q 6)) = q.stabPath := by
    ext g
    constructor
    · rintro ⟨hg1, hgx, hg6⟩
      exact CFSG.Quasithin.D4Hex.mem_stabPath_of_fix hpoly hq (MulAction.mem_stabilizer_iff.mp hgx)
        (MulAction.mem_stabilizer_iff.mp hg1) (MulAction.mem_stabilizer_iff.mp hg6)
    · intro hg
      exact ⟨MulAction.mem_stabilizer_iff.mpr (hg 1 (by norm_num)),
        GPath.stabPath_le_stabilizer q hq.1 hg, MulAction.mem_stabilizer_iff.mpr (hg 6 le_rfl)⟩
  have h1 := Subgroup.relIndex_mul_card (stv c (q 1)) (stv c c.xv ⊓ stv c (q 6))
  rw [hst, burnsideF45_relIndex_stv, horb, ← Nat.card_coe_set_eq, hn3] at h1
  rcases h9 (q 6) hv with h | h <;> omega

theorem burnsideF46_g2d_relIndex_of {Q : Subgroup c.G0} (hQx : Q ≤ stv c c.xv)
    (hfix : ∀ w, c.graph.Adj c.xv w → Q ≤ stv c w) {w : c.Γ} (hw : c.graph.Adj c.xv w)
    (htr : ∀ w₁ ∈ CosetGeom.nbrs c.xv \ {w}, ∀ w₂ ∈ CosetGeom.nbrs c.xv \ {w},
      ∃ g ∈ stv c c.xv ⊓ stv c w, g • w₁ = w₂)
    (hker : ∀ g ∈ stv c c.xv ⊓ stv c w, ∀ w' ∈ CosetGeom.nbrs c.xv \ {w}, g • w' = w' → g ∈ Q)
    (hcard : Nat.card ↥(CosetGeom.nbrs c.xv \ {w}) = 2) {w' : c.Γ}
    (hw'm : w' ∈ CosetGeom.nbrs c.xv \ {w}) :
    Q.relIndex (stv c c.xv ⊓ stv c w) = 2 := by
  have hw' : c.graph.Adj c.xv w' := hw'm.1
  have hw'w : w' ≠ w := hw'm.2
  have hstw : stv c w' ⊓ (stv c c.xv ⊓ stv c w) = Q := by
    refine le_antisymm ?_ (le_inf (hfix _ hw') (le_inf hQx (hfix _ hw)))
    rintro g ⟨hgw', hgB⟩
    exact hker g hgB w' hw'm (MulAction.mem_stabilizer_iff.mp hgw')
  have horb : MulAction.orbit ↥(stv c c.xv ⊓ stv c w) w' = CosetGeom.nbrs c.xv \ {w} := by
    ext t
    constructor
    · rintro ⟨g, rfl⟩
      have hgx : (g : c.G0) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp g.2.1
      have hgw : (g : c.G0) • w = w := MulAction.mem_stabilizer_iff.mp g.2.2
      refine ⟨?_, ?_⟩
      · show c.graph.Adj c.xv ((g : c.G0) • w')
        have := (GraphAction.adj_smul (g : c.G0) c.xv w').mpr hw'
        rwa [hgx] at this
      · intro h
        rw [Set.mem_singleton_iff] at h
        exact hw'w (smul_left_cancel _ (h.trans hgw.symm))
    · intro ht
      obtain ⟨g, hg, hgt⟩ := htr w' hw'm t ht
      exact ⟨⟨g, hg⟩, hgt⟩
  rw [← hstw, Subgroup.inf_relIndex_right, burnsideF45_relIndex_stv, horb, ← Nat.card_coe_set_eq,
    hcard]

end CFSG.ASVolI
