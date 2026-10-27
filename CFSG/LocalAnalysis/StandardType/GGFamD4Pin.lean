module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLRankFour
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Layers
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

theorem d4_selected_pin_of_prime
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ N : ℕ}
    (S : LangSetup τ L p₀) (hN : N.Prime) (hNL : (N : L) ≠ 0)
    (b : Fin τ.rank → Lˣ) (hbN : rootDiagUnit τ b ^ N = 1)
    (j : KernelComponent (rootCharHom b))
    (hr : compRank (componentRoots (rootCharHom b) j) = 4)
    (hc : (componentRoots (rootCharHom b) j).ncard = 24) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom b) j =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨v, μ, -, hpinned⟩ :=
      exists_pinnedT_of_pos (a := b) hN.pos hNL facts_E6 hbN
    obtain ⟨x, C, -, -, hi, hrank, hcard⟩ := hpinned j
    have hC : C = ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E6.rank))) :=
      kacCount_E6_four C (hrank ▸ hr) (hcard ▸ hc)
    refine ⟨v, ?_⟩
    rw [hi, hC, kacE6.rootsOf_eq_parabolicRoots (by decide)]
    congr 2
    exact Set.ext fun k => by simp only [d4Nodes, Set.mem_setOf_eq]; revert k; decide
  · obtain ⟨v, μ, -, hpinned⟩ :=
      exists_pinnedT_of_pos (a := b) hN.pos hNL facts_E7 hbN
    obtain ⟨x, C, -, -, hi, hrank, hcard⟩ := hpinned j
    have hC : C = ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E7.rank))) :=
      kacCount_E7_four C (hrank ▸ hr) (hcard ▸ hc)
    refine ⟨v, ?_⟩
    rw [hi, hC, kacE7.rootsOf_eq_parabolicRoots (by decide)]
    congr 2
    exact Set.ext fun k => by simp only [d4Nodes, Set.mem_setOf_eq]; revert k; decide
  · obtain ⟨v, μ, -, hpinned⟩ :=
      exists_pinnedT_of_pos (a := b) hN.pos hNL facts_E8 hbN
    obtain ⟨x, C, -, -, hi, hrank, hcard⟩ := hpinned j
    have hC : C = ({some 1, some 2, some 3, some 4} : Finset (Option (Fin Tag.E8.rank))) :=
      kacCount_E8_four C (hrank ▸ hr) (hcard ▸ hc)
    refine ⟨v, ?_⟩
    rw [hi, hC, kacE8.rootsOf_eq_parabolicRoots (by decide)]
    congr 2
    exact Set.ext fun k => by simp only [d4Nodes, Set.mem_setOf_eq]; revert k; decide

end CFSG.StandardType.TableCRes
