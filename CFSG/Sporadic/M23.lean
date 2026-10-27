module

public import CFSG.Sporadic.M23.DeletedPermutation
public import CFSG.Sporadic.M23.IsotypicCount
public import CFSG.Sporadic.M23.M23Simplicity

public section

namespace CFSG

open scoped TensorProduct MonoidAlgebra

namespace M23

theorem m23_irrep_tensor_square_decomp :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 10200960 ∧
      IsSimpleGroup G ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ G V),
        Module.finrank ℂ V = 22 ∧
        ρ.IsIrreducible ∧
        (@isotypicComponents (MonoidAlgebra ℂ G) (V ⊗[ℂ] V) _ _
          (Module.compHom (V ⊗[ℂ] V)
            (Representation.asAlgebraHom (ρ.tprod ρ)).toRingHom)).ncard = 4 := by
  let : MulAction.IsMultiplyPretransitive M23Group.H0 (Fin 23) 4 :=
    M23Group.four_pretransitive
  refine ⟨M23Group.H0, inferInstance, inferInstance, M23Group.card_M23,
    M23Group.isSimpleGroup_H0, ?_⟩
  let V := DeletedPermutation.V
  let ρ : Representation ℂ M23Group.H0 V := DeletedPermutation.deletedRep
  refine ⟨V, inferInstance, inferInstance, ρ, ?_, ?_, ?_⟩
  · simp [V, DeletedPermutation.V]
  · exact DeletedPermutation.deletedRep_isIrreducible
  · have hcard_ne : (Nat.card M23Group.H0 : ℂ) ≠ 0 := by
      norm_cast
      exact Nat.ne_of_gt (Nat.card_pos (α := M23Group.H0))
    let : NeZero (Nat.card M23Group.H0 : ℂ) := ⟨hcard_ne⟩
    let ρ2 : Representation ℂ M23Group.H0 (V ⊗[ℂ] V) := ρ.tprod ρ
    have hrank : Module.finrank ℂ (ρ2.IntertwiningMap ρ2) = 4 := by
      simpa [ρ2, ρ, V] using
        (DeletedPermutation.tensor_intertwining_finrank (G := M23Group.H0))
    have hinv : Module.finrank ℂ ρ2.invariants = 1 := by
      simpa [ρ2, ρ, V] using
        (DeletedPermutation.tensor_invariants_finrank (G := M23Group.H0))
    have hdim : 1 < Module.finrank ℂ (V ⊗[ℂ] V) := by
      rw [Module.finrank_tensorProduct]
      norm_num [V, DeletedPermutation.V]
    have htwo :
        2 ≤ (isotypicComponents ℂ[M23Group.H0] ρ2.asModule).ncard :=
      two_le_ncard_isotypicComponents_of_finrank_invariants_eq_one
        ρ2 hinv hdim
    have hn : (isotypicComponents ℂ[M23Group.H0] ρ2.asModule).ncard = 4 :=
      ncard_isotypicComponents_asModule_eq_four ρ2 hrank htwo
    exact hn

end M23

end CFSG
