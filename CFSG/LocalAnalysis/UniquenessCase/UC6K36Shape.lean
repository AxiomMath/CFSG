module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Concl
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open CFSG.ASVolI.ChIJK (IsGraphFieldAut F4)
open scoped MatrixGroups

@[expose] def ShapeComp {G : Type} [Group G] (t : G) (K : Subgroup G) : Prop :=
  ((Nonempty (↥K ≃* PSL(3, F4)) ∨ Nonempty (↥K ≃* SL(3, F4))) ∧ UC6.InducesGraphField t K) ∨
    (Nonempty (↥K ≃* alternatingGroup (Fin 11)) ∧ UC6.InducesTransposition t K)

@[expose] def L34OuterFree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], (Nonempty (K ≃* PSL(3, F4)) ∨ Nonempty (K ≃* SL(3, F4))) →
    ∀ τ ε : MulAut K, IsGraphFieldAut τ → τ * τ = 1 → ε * ε * ε = 1 → τ * ε = ε * τ →
      (∀ k : K, ε k = k → τ k = k) → ∃ g : K, ∀ x : K, ε x = g * x * g⁻¹

end CFSG.LocalAnalysis.UniquenessCase.UCK
