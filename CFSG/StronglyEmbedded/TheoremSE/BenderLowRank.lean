module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

public section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

noncomputable section

theorem twoRankAtLeastTwo_of_injective
    {G K : Type*} [Group G] [Group K] [Finite G] [Finite K]
    (f : G →* K) (hf : Function.Injective f)
    (hG : TwoRankAtLeastTwo G) : TwoRankAtLeastTwo K := by
  obtain ⟨E, hcard, hsquare⟩ := hG
  refine ⟨E.map f, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf]
    exact hcard
  · rintro ⟨x, y, hy, rfl⟩
    apply Subtype.ext
    exact (map_pow f y 2).symm.trans
      (by simpa using congrArg (fun z : E => f z) (hsquare ⟨y, hy⟩))

theorem twoRankAtLeastTwo_involutionCore_iff
    {X : Type*} [Group X] [Finite X] :
    TwoRankAtLeastTwo (involutionCore X) ↔ TwoRankAtLeastTwo X := by
  constructor
  · exact twoRankAtLeastTwo_of_injective (involutionCore X).subtype
      Subtype.val_injective
  · rintro ⟨E, hcard, hsquare⟩
    have hEcore : E ≤ involutionCore X := by
      intro x hx
      by_cases hxone : x = 1
      · simp [hxone]
      · rw [involutionCore_eq_closure]
        apply Subgroup.subset_closure
        refine ⟨hxone, ?_⟩
        exact congrArg Subtype.val (hsquare ⟨x, hx⟩)
    let f : E →* involutionCore X :=
      E.subtype.codRestrict (involutionCore X) (fun x => hEcore x.property)
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : involutionCore X => (z : X)) h
    refine ⟨(⊤ : Subgroup E).map f, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top]
      exact hcard
    · rintro ⟨x, y, _hy, rfl⟩
      apply Subtype.ext
      exact (map_pow f y 2).symm.trans (by simpa using congrArg f (hsquare y))

theorem sylowTwo_cyclic_or_quaternion_of_not_twoRank
    {X : Type*} [Group X] [Finite X] (hX : ¬ TwoRankAtLeastTwo X) :
    ∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  classical
  intro S
  by_cases hS : Nontrivial S
  · let : Nontrivial S := hS
    have hrank : ¬ TwoRankAtLeastTwo S := by
      intro hrank
      exact hX (twoRankAtLeastTwo_of_injective
        (S : Subgroup X).subtype Subtype.val_injective hrank)
    have hunique := PFAppendixII.unique_order_two_subgroup_of_not_twoRank
      S.isPGroup' hrank
    exact (External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
      Nat.prime_two S.isPGroup' hunique).2 rfl
  · let : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    exact Or.inl inferInstance

end

end CFSG.BenderSuzuki
