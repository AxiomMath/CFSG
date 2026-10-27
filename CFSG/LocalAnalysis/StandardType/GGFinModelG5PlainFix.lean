module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section PlainFix

theorem ggG5_phi_canonicalRep_untw
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (f : ℕ) (u : WeylGroup (langTag t)) :
    ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
      canonicalRep (coxeterSystem (langTag t)) GGL u := by
  rcases ht with rfl | rfl | rfl | rfl
  · change Units.map (entrywiseHom (ggFrobT f))
        (canonicalRep (coxeterSystem Tag.F4) GGL u) =
      canonicalRep (coxeterSystem Tag.F4) GGL u
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL]
    exact CFSG.LieType.Chevalley.baseChangeGL_canonicalRep (ggFrobT f) u
  · change Units.map (entrywiseHom (ggFrobT f))
        (canonicalRep (coxeterSystem Tag.E6) GGL u) =
      canonicalRep (coxeterSystem Tag.E6) GGL u
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL]
    exact CFSG.LieType.Chevalley.baseChangeGL_canonicalRep (ggFrobT f) u
  · change Units.map (entrywiseHom (ggFrobT f))
        (canonicalRep (coxeterSystem Tag.E7) GGL u) =
      canonicalRep (coxeterSystem Tag.E7) GGL u
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL]
    exact CFSG.LieType.Chevalley.baseChangeGL_canonicalRep (ggFrobT f) u
  · change Units.map (entrywiseHom (ggFrobT f))
        (canonicalRep (coxeterSystem Tag.E8) GGL u) =
      canonicalRep (coxeterSystem Tag.E8) GGL u
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL]
    exact CFSG.LieType.Chevalley.baseChangeGL_canonicalRep (ggFrobT f) u

theorem ggG5_phi_canonicalRep_twistedE6
    (f : ℕ) (u : WeylGroup TwistTag.E6.tag)
    (hu : weylTwist TwistTag.E6 u = u) :
    ggPhi .twistedE6 f (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL u) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) GGL u := by
  change twistHom TwistTag.E6 GGL (ggFrobT f)
      (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL u) = _
  rw [CFSG.LieType.Chevalley.twistHom_canonicalRep, hu]

end PlainFix

end CFSG.StandardType.GGFinModel.G5
