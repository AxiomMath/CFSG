module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45SpGeomBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Assembly

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Blueprint CFSG.ComponentClassification.UnbalancedCatalog.SpChain

namespace F45

open SpGeom

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem spGeomFacts : SpGeomFacts F (Gr F) (Sum.inl (pt0 : Pt F)) (Sum.inr (ln0 : Ln F)) where
  poly := isGenPolygon_gr
  adj := incGraph_adj_inl_inr.mpr inc_pt0_ln0
  disj y z := by
    rw [Sum.smul_inl, Sum.smul_inr]
    exact Sum.inl_ne_inr
  noadj_p y z := by
    rw [Sum.smul_inl, Sum.smul_inl]
    exact fun h => h
  noadj_l y z := by
    rw [Sum.smul_inr, Sum.smul_inr]
    exact fun h => h
  stab_p y := by
    rw [Sum.smul_inl, Sum.inl.injEq]
    exact stab_pt0_iff y
  stab_l y := by
    rw [Sum.smul_inr, Sum.inr.injEq]
    exact stab_ln0_iff y
  three_p := three_pt0
  three_l := three_ln0
  base_p := modelBase_pt0
  base_l := modelBase_ln0

theorem spGeomProp (F : Type) [Field F] [Finite F] [CharP F 2] : SpGeomProp F :=
  ⟨Pt F ⊕ Ln F, inferInstance, Gr F, inferInstance, Sum.inl pt0, Sum.inr ln0, spGeomFacts⟩

end F45

theorem f431Facts45_psp (f : ℕ) (hm : F431ModelFacts .PSp 2 f) : F431Facts45 .PSp 2 f hm :=
  fun _ _ hD A => F45.facts45L_of_spGeom hD A (hm _ hD).1 fun F _ _ _ => F45.spGeomProp F

end CFSG.Quasithin.H13.F431
