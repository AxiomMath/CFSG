module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2Excl
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReal
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.LocalAnalysis.GLTheoremA CFSG.Open
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggNbrLSideRSExc_u2_nonA
    (hExcl : GGNbrLSideRSExcExcl) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (h2 : (2 : L) = 0) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {Q : ℕ}
    (hP : GGNbrLSideRSExcPSL3 S a i Q) (hA : ¬ L154TypeAClass a i) (hE : ¬ L154E6Class a i) :
    False := by
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by simpa using h2)
  obtain ⟨hT, hp3, hne, hqs, hQ4, h3Q, F, hFf, hFin, hFc, ⟨e⟩⟩ := hP
  have hcls : L154Cls S 3 a i := ⟨Nat.prime_three, by norm_num, hT, hp3, hne, hqs⟩
  have hmod : L154ClassModel S i :=
    l154NonCfgModels_of_residuals l154F4Models_holds l154Rank4Models_holds τ L p₀ S 3 a i
      hcls hA hE
  have hF4 : 4 ≤ Nat.card F := hFc ▸ hQ4
  rcases hmod with ⟨t, n, f, hLie, hgood⟩ | ⟨⟨e6⟩⟩
  · obtain ⟨htp, hn3, -⟩ := hExcl hF4 e hLie
    subst htp
    subst hn3
    rcases hgood with ⟨-, h⟩ | h | h | h | h | h | h | h | h <;> first | omega | cases h
  · have hcard := Nat.card_congr (e.toEquiv.symm.trans e6.toEquiv)
    have hbig := ggNbrLSidePSL3_card_gt hF4
    have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    omega

end CFSG.StandardType
