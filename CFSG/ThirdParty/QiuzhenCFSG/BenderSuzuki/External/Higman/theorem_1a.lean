module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem for Suzuki 2-groups: extracted branch
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u
/-- Theorem 1(a), in the form quoted in Peterfalvi Appendix III: the
involutions are precisely the nonidentity central elements, and the center has
exponent two. -/
public theorem theorem1_involutions_center
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) :
    involutions P = {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} ∧
      ∀ z : Subgroup.center P, z ^ 2 = 1 := by
  have hinvolutions_le_center :
      involutions P ⊆ {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} := by
    rcases hP.2.2.2 with
      ⟨X, hXGroup, hXAction, _hXcyclic, _hXfaithful, hXregular⟩
    letI : Group X := hXGroup
    letI : MulDistribMulAction X P := hXAction
    have hXtrans : ∀ x : P, x ∈ involutions P →
        ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x := by
      intro x hx y hy
      rcases hXregular.2 x hx y hy with ⟨k, hk, _hunique⟩
      exact ⟨k, hk⟩
    letI : Finite P := finite_of_isSuzukiTwoGroup hP
    letI : Nontrivial P := by
      rcases hP.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
      exact ⟨⟨x, y, hxy⟩⟩
    have hcenter_ne : Subgroup.center P ≠ ⊥ :=
      ne_of_gt (isPGroup_of_isSuzukiTwoGroup hP).bot_lt_center
    have hcenter_X : IsXInvariantSubgroup X (Subgroup.center P) :=
      isXInvariantSubgroup_center X P
    intro z hz
    exact ⟨lemma1_involutions_mem_of_nontrivial_invariant
      hP hXtrans hcenter_X hcenter_ne z hz, hz.ne_one⟩
  have hcenter_exponent_two :
      ∀ z : Subgroup.center P, z ^ 2 = 1 := by
    rcases theorem1b_abcdAlternatives hP with hA | hB | hC | hD
    · exact (theorem1b_typeA_data hA).2.1
    · exact (theorem1b_typeB_data hB).2.1
    · exact (theorem1b_typeC_data hC).2.1
    · exact (theorem1b_typeD_data hD).2.1
  have hcenter_nontrivial_le_involutions :
      {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} ⊆ involutions P := by
    intro z hz
    exact ⟨hz.2, by
      simpa using congrArg Subtype.val
        (hcenter_exponent_two ⟨z, hz.1⟩)⟩
  exact ⟨Set.Subset.antisymm hinvolutions_le_center
    hcenter_nontrivial_le_involutions, hcenter_exponent_two⟩
end Higman
end External
end CFSG.BenderSuzuki
