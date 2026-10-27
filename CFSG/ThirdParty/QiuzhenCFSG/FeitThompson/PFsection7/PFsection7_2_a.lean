module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_1

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_2_a_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) : Prop :=
  hypothesis_7_1_statement A L H →
    ∀ α : Section1.ClassFunction L,
      Section2.CFOn L A α →
        ∀ a : L, (a : G) ∈ A →
          dadeProjection L H (Section2.dadeTransform H hAL α) a = α a

/-- Peterfalvi `(7.2)(b)`. -/


public theorem theorem_7_2_a
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) :
    theorem_7_2_a_statement A L H hAL := by
  intro h71 α hα a ha
  classical
  have hdef := Section2.definition_2_5 A L H h71 hAL α hα
  have hvalue : ∀ x : H (a : G),
      Section2.dadeTransform H hAL α ((a : G) * (x : G)) = α a := by
    intro x
    have hconj : Section2.conjugateIn ((a : G) * (x : G)) ((a : G) * (x : G)) := by
      refine ⟨1, ?_⟩
      simp [Section2.conjBy]
    have hv := (hdef.1)
      (g := (a : G) * (x : G)) (a := (a : G)) (h' := (x : G)) ha x.2 hconj
    simpa using hv
  have hcard_univ :
      (@Finset.univ (H (a : G)) (Fintype.ofFinite (H (a : G)))).card =
        Nat.card (H (a : G)) := by
    change @Fintype.card (H (a : G)) (Fintype.ofFinite (H (a : G))) =
      Nat.card (H (a : G))
    exact (@Nat.card_eq_fintype_card (H (a : G)) (Fintype.ofFinite (H (a : G)))).symm
  have hcardNat_ne : (Nat.card (H (a : G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H (a : G))).ne'
  unfold dadeProjection Section2.dadeAveragingFunction
  simp only [hvalue, Finset.sum_const, nsmul_eq_mul]
  rw [hcard_univ]
  field_simp [hcardNat_ne]

end CFSG.Section7
