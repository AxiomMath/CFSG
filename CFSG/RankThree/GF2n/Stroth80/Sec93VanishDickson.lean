module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

theorem even_finrank_of_mem_statedOmega {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {A : GL (Fin 2 ⊕ Fin 2) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus 2 K)) :
    Even (Module.finrank K (LinearMap.range
      (Matrix.toLin' (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - LinearMap.id))) := by
  obtain ⟨c0, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun c _ => by
      by_cases hc : c = 0
      · exact Or.inl hc
      · exact Or.inr (h c hc)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at h1
    omega
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K
  have E : ElemMatrixIso (CFSG.LieType.Universal.Spin.quadPlus 2 K)
      (StatedOmega (StatedQuadPlus 2 K)) :=
    ElemMatrixIso.ofStated (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K)
      (CFSG.RankThree.GF2n.Stroth80.Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)
  obtain ⟨g, hgA⟩ : ∃ g : Gom (CFSG.LieType.Universal.Spin.quadPlus 2 K),
      ∀ v : Fin 2 ⊕ Fin 2 → K,
        (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) v =
          (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v :=
    ⟨E.equiv ⟨A, hA⟩, fun v => E.app ⟨A, hA⟩ v⟩
  have hmem : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (CFSG.LieType.Universal.Spin.quadPlus 2 K) hQ :=
    elementaryGroup_le_omegaGroup hQ g.2
  obtain ⟨-, hev⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hmem
  have hlin : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)).toLinearMap =
      Matrix.toLin' (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply]
    exact hgA v
  have hcs : CFSG.RankThree.OrthogonalInvolutions.commSpace
      (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) =
      LinearMap.range (Matrix.toLin' (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) := by
    rw [CFSG.RankThree.OrthogonalInvolutions.commSpace, ← hlin]
  rw [hcs] at hev
  exact hev

end CFSG.RankThree.GF2n.Stroth80
