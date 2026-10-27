module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Link
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LinkF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem

namespace CFSG.StandardType.LieKnownR2.ExcNC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

theorem rootNoCentral_highRoot_exc
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    GGRootNoCentralAt (adjointGroup τ K) (rootSubgroup τ K (highRoot τ)) := by
  have key : ∀ (τ : Tag), (∃ h ∈ Pθ τ K, Odd (orderOf h) ∧
      ∀ q ∈ Qθ τ K, h * q * h⁻¹ * q⁻¹ ∈ Uθ τ K → q ∈ Uθ τ K) →
      GGRootNoCentralAt (adjointGroup τ K) (rootSubgroup τ K (highRoot τ)) := by
    intro τ hex
    obtain ⟨h, hhP, hodd, hfpf⟩ := hex
    have hC2 := even_highest_root_normalizer τ K
    have hN_eq : adjointGroup τ K ⊓
        Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) =
        parabolicSubgroup τ K (Jθ τ) := by
      rw [inf_comm]
      exact hC2.1
    have hhN : h ∈ adjointGroup τ K ⊓
        Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) := by
      rw [hN_eq]
      exact hhP
    have hfix : ∀ y ∈ pCoreOf 2 (adjointGroup τ K ⊓
        Subgroup.normalizer (Uθ τ K : Set (ModGL τ K))),
        h * y = y * h → y ∈ Uθ τ K := by
      intro y hy hyh
      have hy' : y ∈ parabolicRadical τ K (Jθ τ) ⊓ adjointGroup τ K := by
        rw [hN_eq, hC2.2] at hy
        exact hy
      have h1 : h * y * h⁻¹ * y⁻¹ = 1 := by
        rw [hyh]
        group
      exact hfpf y (Subgroup.mem_inf.mp hy').1 (by rw [h1]; exact (Uθ τ K).one_mem)
    haveI : Finite (ModGL τ K) := finite_modGL
    exact noCentral_of_fixedPoint_odd hodd hhN hfix
  rcases hτ with rfl | rfl | rfl | rfl
  · exact key .E6 (Link.E6_exists_odd_fpf K)
  · exact key .E7 (Link.E7_exists_odd_fpf K)
  · exact key .E8 (Link.E8_exists_odd_fpf K)
  · exact key .F4 (LinkF4.F4_exists_odd_fpf K)

end CFSG.StandardType.LieKnownR2.ExcNC
