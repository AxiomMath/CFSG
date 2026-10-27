module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.ConjSub
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.LangLeviAux
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Plane
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.EmptyFaithful.T1515C6Grp
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups

open scoped CFSG.ConvolutionPoints

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

open CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.AlgebraicGroups WithConv

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.PairStabilizer

variable (τ : Tag) (K : Type) [Field K]

theorem adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg_eq_Lθ :
    adjointGroup τ K ⊓ Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (Uneg τ K : Set (ModGL τ K)) = Lθ τ K := by
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgP, hgNneg⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgA, hgNθ⟩ := Subgroup.mem_inf.1 hgP
    exact Pθ_inf_Pneg_le_Lθ τ K (normalizer_Uθ_le_Pθ τ K hgA hgNθ) ⟨hgA, hgNneg⟩
  · intro g hg
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact Pθ_le_adjointGroup τ K (Lθ_le_Pθ τ K hg)
    · exact Pθ_le_normalizer_Uθ τ K (Lθ_le_Pθ τ K hg)
    · exact Lθ_le_normalizer_Uneg τ K hg

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame in
theorem isConnectedAlgebraicSubgroup_adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg
    [IsAlgClosed K] :
    IsConnectedAlgebraicSubgroup K
      ((adjointGroup τ K ⊓ Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (Uneg τ K : Set (ModGL τ K))).map
          (modGLPoint τ K).toMonoidHom) := by
  rw [adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg_eq_Lθ]
  exact LangLeviAux.isConnectedAlgebraicSubgroup_parabolicLevi
    (τ := τ) (k := K) (Jθ τ)

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame in
theorem frobTwistGL_one_mem_adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] (e : ℕ) {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K ⊓ Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (Uneg τ K : Set (ModGL τ K))) :
    frobTwistGL τ K p e 1 g ∈ adjointGroup τ K ⊓
        Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) ⊓
        Subgroup.normalizer (Uneg τ K : Set (ModGL τ K)) := by
  rw [adjointGroup_inf_normalizer_Uθ_inf_normalizer_Uneg_eq_Lθ] at hg ⊢
  exact LangLeviAux.frobTwistGL_one_mem_parabolicLevi
    (τ := τ) (k := K) p e (Jθ τ) hg

end CFSG.StandardType.F4ExplicitPos.PairStabilizer

end
end
end
end

end
