module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.OneFixerSuccessorTransitivity

open MulAction SubMulAction

theorem succ_of_one_transitive_fixing
    (G X : Type*) [Group G] [MulAction G X] (k : ℕ)
    (hk : IsMultiplyPretransitive G X k) (e : Fin k ↪ X)
    (hfix : IsPretransitive (fixingSubgroup G (Set.range e))
      (ofFixingSubgroup G (Set.range e))) :
    IsMultiplyPretransitive G X (k + 1) := by
  rw [isMultiplyPretransitive_iff] at hk ⊢
  intro a b
  let a0 : Fin k ↪ X := ⟨fun i => a i.castSucc, a.injective.comp (Fin.castSucc_injective k)⟩
  let b0 : Fin k ↪ X := ⟨fun i => b i.castSucc, b.injective.comp (Fin.castSucc_injective k)⟩
  obtain ⟨g, hg⟩ := hk a0 e
  obtain ⟨h, hh⟩ := hk b0 e
  have hglast : g • a (Fin.last k) ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have he := (DFunLike.congr_fun hg i).trans hi
    exact Fin.castSucc_ne_last i (a.injective (smul_left_cancel g he))
  have hhlast : h • b (Fin.last k) ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have he := (DFunLike.congr_fun hh i).trans hi
    exact Fin.castSucc_ne_last i (b.injective (smul_left_cancel h he))
  obtain ⟨q, hq⟩ := hfix.exists_smul_eq
    (⟨g • a (Fin.last k), hglast⟩ : ofFixingSubgroup G (Set.range e))
    (⟨h • b (Fin.last k), hhlast⟩ : ofFixingSubgroup G (Set.range e))
  refine ⟨h⁻¹ * q.val * g, ?_⟩
  ext i
  change (h⁻¹ * q.val * g) • a i = b i
  rw [mul_smul, mul_smul]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [show g • a j.castSucc = e j from DFunLike.congr_fun hg j]
    rw [(mem_fixingSubgroup_iff G).mp q.property _ ⟨j, rfl⟩]
    rw [← show h • b j.castSucc = e j from DFunLike.congr_fun hh j, inv_smul_smul]
  · have hq' : q.val • (g • a (Fin.last k)) = h • b (Fin.last k) :=
      congrArg Subtype.val hq
    rw [hq', inv_smul_smul]

end FiveTransitive.OneFixerSuccessorTransitivity

end CFSG
