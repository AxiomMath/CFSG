module

public import CFSG.RankThree.GF2n.Smith81.S81QCore
public import CFSG.RankThree.GF2n.Smith81.S81ZUniformE4
public import CFSG.RankThree.GF2n.Smith81.S81E4Stab

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81


theorem fixP_rad0_eq {K : Type} [Field K] [CharP K 2] [Finite K] {X : Type} [AddCommGroup X] [Module K X]
    (A : ↥(EAut0 K) →* (X ≃ₗ[K] X)) : S81Z.fixP A (S81Z.rad0 K) = fix0 A :=
  Submodule.ext fun _ => Iff.rfl

theorem V1P_rad0_eq {K : Type} [Field K] [CharP K 2] [Finite K] {X : Type} [AddCommGroup X] [Module K X]
    (A : ↥(EAut0 K) →* (X ≃ₗ[K] X)) (β : X →ₗ[K] X →ₗ[K] K) :
    S81Z.V1P A (S81Z.rad0 K) β = V1_0 A β := by
  refine Submodule.ext fun w => ?_
  rw [S81Z.mem_V1P, mem_V1_0, fixP_rad0_eq]
  exact Iff.rfl

theorem e4Core_of_stabChar (K : Type) [Field K] [Finite K] [CharP K 2] (hChar : E4StabChar K) :
    S81Z.E4CoreStatement K := by
  intro hq X _ _ hX A β hβalt hβA hline hspan hV1
  rw [fixP_rad0_eq] at hline hspan
  rw [V1P_rad0_eq] at hV1
  obtain ⟨σ, ψ, h1, h2⟩ := core_main_E4 hq hChar hX A β hβalt hβA hline hspan hV1
  refine ⟨σ, ψ, h1, ?_⟩
  rw [fixP_rad0_eq]
  exact h2

theorem e4Core_holds (K : Type) [Field K] [Finite K] [CharP K 2] : S81Z.E4CoreStatement K :=
  e4Core_of_stabChar K (e4StabChar_holds K)

end CFSG.RankThree.GF2n.Smith81.D6Spin
