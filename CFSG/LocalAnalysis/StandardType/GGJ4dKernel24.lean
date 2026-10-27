module

public import CFSG.LocalAnalysis.StandardType.GGJ4dStable
public import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLangLayer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoOrders
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Dickson.Sec6

theorem j4d_image_eq_of_componentOrbitLength_eq_one
    {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : componentOrbitLength ρ Ψ = 1) :
    (ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ := by
  classical
  have hne : {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}.Nonempty := by
    by_contra h'
    rw [Set.not_nonempty_iff_eq_empty] at h'
    have hzero : componentOrbitLength ρ Ψ = 0 := by
      unfold componentOrbitLength
      rw [h', Nat.sInf_empty]
    omega
  have hmem := Nat.sInf_mem hne
  have hmem1 : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} := by
    rw [← h]
    exact hmem
  simpa only [Function.iterate_one] using hmem1.2

end CFSG.StandardType.LangRat

end
