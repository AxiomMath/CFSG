module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Ctx
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45PgBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace F45

open PgGeom

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem smul_p0_iff_normalizer (y : projectiveSL 3 F) :
    y • (p0 : Pt F) = p0 ↔
      y ∈ Subgroup.normalizer ((Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) : Set _) := by
  rw [smul_p0_iff, L3.P3.normalizer_V1_eq]
  rfl

theorem smul_l0_iff_normalizer (y : projectiveSL 3 F) :
    y • (l0 : Ln F) = l0 ↔
      y ∈ Subgroup.normalizer ((Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) : Set _) := by
  rw [smul_l0_iff, L3.P3.normalizer_V2_eq]
  rfl

theorem stabilizer_inl_p0 :
    MulAction.stabilizer (projectiveSL 3 F) (Sum.inl (p0 : Pt F) : Pt F ⊕ Ln F) =
      Subgroup.normalizer ((Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) : Set _) := by
  ext y
  rw [MulAction.mem_stabilizer_iff, Sum.smul_inl, Sum.inl.injEq]
  exact smul_p0_iff_normalizer y

theorem stabilizer_inr_l0 :
    MulAction.stabilizer (projectiveSL 3 F) (Sum.inr (l0 : Ln F) : Pt F ⊕ Ln F) =
      Subgroup.normalizer ((Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) : Set _) := by
  ext y
  rw [MulAction.mem_stabilizer_iff, Sum.smul_inr, Sum.inr.injEq]
  exact smul_l0_iff_normalizer y

end F45

open F45 in
theorem f431Facts45_psl (f : ℕ) (hm : F431ModelFacts .PSL 3 f) : F431Facts45 .PSL 3 f hm := by
  intro D _ hD A
  obtain ⟨F, hFf, hFfin, hFchar, E, hFcard, hcases⟩ := L3.l3Amalgam_borel hD A
  have hgen := f431Generation_psl3 f D hD A
  have hcen := (hm D hD).2
  have hb := Borel252.L3.borelData_L3 (F := F)
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have X := F45.xdatum_of_inn A (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL) E hgen
      hcen h1 h2 hb.core₁ hb.core₂ (PgGeom.Gr F) (Sum.inl (PgGeom.p0 : PgGeom.Pt F))
      (Sum.inr (PgGeom.l0 : PgGeom.Ln F))
      (fun y => by
        rw [Sum.smul_inl, Sum.inl.injEq]
        exact F45.smul_p0_iff_normalizer y)
      (fun y => by
        rw [Sum.smul_inr, Sum.inr.injEq]
        exact F45.smul_l0_iff_normalizer y)
      (fun y z => by
        rw [Sum.smul_inl, Sum.smul_inr]
        exact Sum.inl_ne_inr)
      (fun y z => by
        rw [Sum.smul_inl, Sum.smul_inl]
        exact fun h => h)
      (fun y z => by
        rw [Sum.smul_inr, Sum.smul_inr]
        exact fun h => h)
      (F45.incGraph_adj_inl_inr.mpr PgGeom.inc_p0_l0)
    exact F45.facts45L_of_model X PgGeom.isGenPolygon_gr PgGeom.three_p0 PgGeom.three_l0
      (Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) (Fin257.L3.V2 : Subgroup (projectiveSL 3 F))
      (by rw [F45.stabilizer_inl_p0]; exact hb.core₁)
      (by rw [F45.stabilizer_inr_l0]; exact hb.core₂) PgGeom.modelBase_p0 PgGeom.modelBase_l0
  · have X := F45.xdatum_of_inn A (hm D hD).1 (polyNumber .PSL) (three_le_polyNumber .PSL) E hgen
      hcen h1 h2 hb.core₂ hb.core₁ (PgGeom.Gr F) (Sum.inr (PgGeom.l0 : PgGeom.Ln F))
      (Sum.inl (PgGeom.p0 : PgGeom.Pt F))
      (fun y => by
        rw [Sum.smul_inr, Sum.inr.injEq]
        exact F45.smul_l0_iff_normalizer y)
      (fun y => by
        rw [Sum.smul_inl, Sum.inl.injEq]
        exact F45.smul_p0_iff_normalizer y)
      (fun y z => by
        rw [Sum.smul_inr, Sum.smul_inl]
        exact Sum.inr_ne_inl)
      (fun y z => by
        rw [Sum.smul_inr, Sum.smul_inr]
        exact fun h => h)
      (fun y z => by
        rw [Sum.smul_inl, Sum.smul_inl]
        exact fun h => h)
      (F45.incGraph_adj_inr_inl.mpr PgGeom.inc_p0_l0)
    exact F45.facts45L_of_model X PgGeom.isGenPolygon_gr PgGeom.three_l0 PgGeom.three_p0
      (Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) (Fin257.L3.V1 : Subgroup (projectiveSL 3 F))
      (by rw [F45.stabilizer_inr_l0]; exact hb.core₂)
      (by rw [F45.stabilizer_inl_p0]; exact hb.core₁) PgGeom.modelBase_l0 PgGeom.modelBase_p0

end CFSG.Quasithin.H13.F431
