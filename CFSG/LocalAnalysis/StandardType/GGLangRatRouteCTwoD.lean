module

public import CFSG.LocalAnalysis.StandardType.GGLangRatRouteCCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDRank
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Models.Transport
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem langRatRouteC_modelPerfect_twoD
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b))
    (hkind : twistKind S.ρ (rootCharHom b) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom b) i)) :
    Group.IsPerfect ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model) := by
  obtain ⟨D, Δ, z, hperf, hΔ, hdet, hspan, hcenter, -, hHmap⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedPointsDatumAt_of_five_le S hb i hkind h5
  have hΔroot : ∀ β ∈ Δ, IsRoot τ β := by
    intro β hβ
    have hβJ : β ∈ D.simpleRootsJ := by rw [← hΔ]; exact hβ
    exact CFSG.LieType.Chevalley.isRoot_of_mem_unionSimpleRoots hβJ.1
  have hP := CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedPointsPerfect_of_datum S D Δ hΔ
    hΔroot hdet hspan hcenter z hHmap hperf
  exact langRatRouteC_modelPerfect_of_fixedData S hb i h5
    (CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedData_of_perfect hP)

end CFSG.StandardType.LangRat

end
