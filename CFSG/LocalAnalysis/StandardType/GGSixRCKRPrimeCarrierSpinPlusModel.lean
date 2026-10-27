module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriKac

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rckSpin_ggU_facts
    {n g : ℕ} (hn : 4 ≤ n) (hg : 0 < g) :
    StandardReturnAt (ggU .POmegaPlus n g) g ∧ Finite (ggU .POmegaPlus n g).K ∧
      Group.IsPerfect (ggU .POmegaPlus n g).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .POmegaPlus n g).K ∧
      ∃ β ∈ (ggU .POmegaPlus n g).D.roots, GGLongRoot (ggU .POmegaPlus n g).D β := by
  have hn3 : 3 ≤ n := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Or.inl ⟨.POmegaPlus, n, Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_, rfl⟩
    change Nat.Prime 2 ∧ 1 ≤ g ∧ 4 ≤ n
    exact ⟨Nat.prime_two, by omega, hn⟩
  · rw [ggU_pOmegaPlus hn3]
    change Finite (spinGroup
      (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 g)))
    exact CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker
      (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 g))
      (@CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus n
        (GaloisField 2 g) inferInstance ⟨by omega⟩)
  · rw [ggU_pOmegaPlus hn3]
    change Group.IsPerfect (spinGroup
      (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 g)))
    exact CFSG.LieType.Universal.Spin.isPerfect_spinGroup_quadPlus hn3
  · rw [ggU_pOmegaPlus hn3]
    change CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit
      (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n (GaloisField 2 g)))
    exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_spinPlus hn3 (GaloisField 2 g)
  · rw [ggU_pOmegaPlus hn3]
    exact CFSG.StandardType.RCKK1I.rckExists_longRoot _ (by change 0 < n; omega)

theorem rckSpin_tag {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1)) :
    τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  cases τ with
  | G2 =>
    exfalso
    have hle : compRank (componentRoots (rootCharHom a) i) ≤ 2 :=
      compRank_le_rank (componentRoots (rootCharHom a) i)
    omega
  | F4 =>
    have hle : compRank (componentRoots (rootCharHom a) i) ≤ 4 :=
      compRank_le_rank (componentRoots (rootCharHom a) i)
    have hr : compRank (componentRoots (rootCharHom a) i) = 4 := le_antisymm hle h4
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hn, hr]
    obtain ⟨N, hN, hNL, hTN⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_exists_order S hT
    exact (CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_F4_absurd
      hN hNL hTN i hr hc).elim
  | D4 => exact Or.inl rfl
  | E6 => exact Or.inr (Or.inl rfl)
  | E7 => exact Or.inr (Or.inr (Or.inl rfl))
  | E8 => exact Or.inr (Or.inr (Or.inr rfl))

end CFSG.StandardType.RCKRP

end
