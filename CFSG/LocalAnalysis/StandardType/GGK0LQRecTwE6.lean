module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
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
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw

private theorem lk0xlqtwe6_rho_stable
    {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  have h6 : 6 ≤ τ.rank := by rcases hτ.isE7E8 with rfl | rfl <;> decide
  rcases hτ.isE7E8 with rfl | rfl
  · refine S.rho_mem_componentRootsT haT i v hΨ (N := 0) (fun s hs => ?_)
      ⟨({Pi.single 0 1} : Finset (Fin Tag.E7.rank → ℤ)), fun α hα => ?_, by simp⟩
    · have := card_le_of_orth_e6 h6 [] (fun l hl h => absurd h (orth_e6_E7 l hl)) s hs
      simpa using this
    · rw [Finset.mem_singleton.1 hα]
      exact single_mem_parabolicRoots_e6 _ (by decide)
  · refine S.rho_mem_componentRootsT haT i v hΨ (N := 6) (fun s hs => ?_)
      ⟨({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
        Pi.single 5 1, Pi.single 0 1 + Pi.single 2 1} : Finset (Fin Tag.E8.rank → ℤ)),
        fun α hα => ?_, by decide⟩
    · exact (card_le_of_orth_e6 h6 _ orth_e6_E8 s hs).trans (by decide)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · refine ⟨isRoot_iff_mem_artifactRoots.2 (by decide), fun j hj => ?_⟩
        have key : ∀ j : Fin 8, ¬ (j.val ≤ 5) →
            ((Pi.single 0 1 + Pi.single 2 1 : Fin 8 → ℤ)) j = 0 := by decide
        exact key j hj

private theorem lk0xlqtwe6_label_of_pinned
    {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.twE6, 0, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  have hL2 : ringChar L = 2 := ringChar.eq L 2
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin (lk0xlqtwe6_rho_stable S haT i v hΨ)
  obtain ⟨f, -, hf, hlie⟩ := lieModel_rationalComponent_of_e6_outer S haT i v hΨ hout
  rw [hL2] at hf hlie
  rw [hs, pow_one, ← hf] at hN
  have hfN : f = N := Nat.pow_right_injective (le_refl 2) hN
  rw [hfN] at hlie
  obtain ⟨-, hm⟩ := hlie.chevalleyExceptionalModel (by decide)
  exact recipeTwisted_of_twistedChevalleyModel .E6 hm

theorem lq_rec_twE6
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.twE6, 0, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hnin, hcases⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exc_kind hk
  have h72 : (componentRoots (rootCharHom a) i).ncard = 72 := by
    rcases hcases with ⟨-, h⟩ | ⟨h4, -, -⟩
    · exact h
    · omega
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 => exact absurd (h6 ▸ hr) (by decide)
  | F4 => exact absurd (h6 ▸ hr) (by decide)
  | D4 => exact absurd (h6 ▸ hr) (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; decide)) h1
  | E7 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i h6 h72
    exact lk0xlqtwe6_label_of_pinned S hT i v hv hnin hN
  | E8 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i h6 h72
    exact lk0xlqtwe6_label_of_pinned S hT i v hv hnin hN

end CFSG.StandardType.GGK0LQ

end
