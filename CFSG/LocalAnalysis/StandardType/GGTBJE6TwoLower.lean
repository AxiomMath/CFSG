module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoWeylPoint
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitFold
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6SplitWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.StandardType.ExcFrames.E6QPlusThree CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp


theorem e6Two_lowerClause {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (S : LangSetup .E6 (AlgebraicClosure K) 5) (hq : S.D.q = Nat.card K)
    (hρ : ∀ β, IsRoot .E6 β → S.ρ β = e6W0 • β)
    (ι : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K)) (hι : Function.Injective ι)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3)
    (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .E6 K)
    (hι₀ : ∀ s, ι (ι₀ s) = e6ThreeDiag ζ hζ s) (hT : ∀ s, e6ThreeDiag ζ hζ s ∈ S.D.torus)
    (t : Fin Tag.F4.rank → ZMod 3) (ht : t ≠ 0)
    (i₆ : KernelComponent
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))))
    {Y : Subgroup (adjointGroup .E6 K)}
    (hY : Y.map ι = rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i₆)
    (hYns : ¬ Group.IsSolvable ↥Y)
    (i₄ : KernelComponent
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))))
    (hB : ∀ γ ∈ componentRoots
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))) i₄,
      ∃ δ ∈ componentRoots
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i₆,
        TwistTag.E6.foldMap γ = TwE6SplitFold.twE6OrbSum δ) :
    ∀ c ∈ componentRoots
        (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 3 t))) i₄,
      ∃ y ∈ Y, ∀ s, y * ι₀ (Multiplicative.ofAdd s) * y⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (rootReflection c) s)) := by
  classical
  intro c hc
  obtain ⟨δ, hδ, hcδ⟩ := hB c hc
  have hδr : IsRoot .E6 δ := (isRootComponent_componentRoots i₆).isRoot δ hδ
  have hns : ¬ Group.IsSolvable ↥(rationalComponent S.ρ S.Γ
      (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t))) i₆) := by
    intro hs
    exact hYns (solvable_of_solvable_injective
      (f := ((Y.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hY)).toMonoidHom)
      ((Y.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hY)).injective)
  have hcr : IsRoot Tag.F4 c := (isRootComponent_componentRoots i₄).isRoot c hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem := e6Two_twE6SplitWeyl_mem_rationalComponent hK S hq hρ hζo hT t ht i₆ hns hδ
  rw [← hY] at hmem
  obtain ⟨y, hyY, hyg⟩ := hmem
  refine ⟨y, hyY, fun s => hι ?_⟩
  rw [map_mul, map_mul, map_inv, hyg, hι₀, hι₀]
  exact twE6SplitWeyl_conj_frameDiag (L := AlgebraicClosure K) (p := 3) hζ hδr hcr hcδ s

end CFSG.StandardType

end
