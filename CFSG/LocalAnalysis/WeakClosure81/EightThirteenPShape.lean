module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

variable {G : Type} [Group G] [Finite G]

@[expose] def ShapeL2Mod (C L : Subgroup G) : Prop :=
  HasQuotShape L (C : Set G) (fun X _ => IsL2 X 2)

@[expose] def ShapeU3Mod (C L : Subgroup G) : Prop :=
  HasQuotShape L (C : Set G) (fun X _ => IsU3 X 2)

@[expose] def ShapeRankTwoMod (C L : Subgroup G) : Prop :=
  HasQuotShape L (C : Set G) (fun X _ => IsL3 X 2) ∨
    HasQuotShape L (C : Set G) (fun X _ => IsSL3 X 2) ∨
    HasQuotShape L (C : Set G) (fun X _ => IsSp4 X 2)

@[expose] def EShape813Gen (C H T A L K : Subgroup G) : Prop :=
  (ShapeL2Mod C L ∨ ShapeU3Mod C L) ∨
    (ShapeRankTwoMod C L ∧
      ((∃ P : Subgroup G, IsMaxParabolicMod C L P ∧ K = oddResMod C P) ∨
        (∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure L H, a * t * a⁻¹ * t⁻¹ ∈ C)))

@[expose] def Case813AB (C L K : Subgroup G) : Prop :=
  ShapeL2Mod C L ∨
    (ShapeRankTwoMod C L ∧ ∃ P : Subgroup G, IsMaxParabolicMod C L P ∧ K = oddResMod C P)

@[expose] def Case813UC (C H T A L : Subgroup G) : Prop :=
  ShapeU3Mod C L ∨
    (ShapeRankTwoMod C L ∧ ∀ a ∈ A, ∀ t ∈ T ⊓ conjClosure L H, a * t * a⁻¹ * t⁻¹ ∈ C)

theorem EShape813Gen.cases {C H T A L K : Subgroup G} (h : EShape813Gen C H T A L K) :
    Case813AB C L K ∨ Case813UC C H T A L := by
  rcases h with (h | h) | ⟨hr, h | h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr ⟨hr, h⟩)
  · exact Or.inr (Or.inr ⟨hr, h⟩)

structure Concl813Gen (C M H T A L K : Subgroup G) : Prop where
  comp : IsComponentModN C H L
  sub_L : K ≤ L
  ge_C : C ≤ K
  a_le : ∀ x ∈ A, ∃ k ∈ K, ∃ t ∈ cenTMod C L T, (k * t)⁻¹ * x ∈ C
  b_not_le : ¬ ∀ x ∈ A, ∃ o ∈ oTwoMod C K, ∃ t ∈ cenTMod C L T, (o * t)⁻¹ * x ∈ C
  c_shape : HasQuotShape K (oTwoMod C K : Set G) (fun X _ => IsL2 X 2)
  d_index : (K ⊓ M).relIndex K = 5
  e_shape : EShape813Gen C H T A L K
  t_sylow : IsSylowIn 2 (T ⊓ K) K

@[expose] def Concl813'' (V H T A L K : Subgroup G) : Prop :=
  Concl813Gen (cGrp H T) (normalizer (V : Set G)) H T A L K

theorem Concl813.eShapeP {V H T A L K : Subgroup G} (h : Concl813 V H T A L K) :
    EShape813Gen (cGrp H T) H T A L K := by
  first
    | exact h.e_shape
    | exact EShape813Gen.of_old h.e_shape

end CFSG.LocalAnalysis.WeakClosure81

end
