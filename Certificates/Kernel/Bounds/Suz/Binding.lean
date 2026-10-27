module

public import Certificates.Kernel.Bounds.Suz.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import Std.Tactic.BVDecide.Normalize.Bool

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Suz

theorem rels_eq : TauCeti.Sporadic.suzPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.suzPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem gens_eq : TauCeti.Sporadic.suzPresentation.generatorCount = 7 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.suzPresentation_generatorNames]

theorem rels_T1_tau : KB.relsOk CFSG.KBData.Suz_T1v.R (nat_lit 34) T1.amap TauCeti.Sporadic.suzPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T1.rels_ok

theorem rels_T2_tau : KB.relsOk CFSG.KBData.Suz_T2v.R (nat_lit 24) T2.amap TauCeti.Sporadic.suzPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T2.rels_ok

theorem rels_T3_tau : KB.relsOk CFSG.KBData.Suz_T3v.R (nat_lit 17) T3.amap TauCeti.Sporadic.suzPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T3.rels_ok

theorem rels_T4_tau : KB.relsOk CFSG.KBData.Suz_T4v.R (nat_lit 11) T4.amap TauCeti.Sporadic.suzPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T4.rels_ok

end CFSG.KBRoute.Suz

end
