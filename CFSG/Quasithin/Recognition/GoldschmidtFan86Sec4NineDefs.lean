module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubDefs

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def H48 (T : Track Γ G) (a : ℤ) : Subgroup G :=
  Subgroup.closure ((↑(Subgroup.normalizer (omega1 T.fixer : Set G) ⊓
      MulAction.stabilizer G (T.line.vert a)) : Set G) ∪
    ↑(Lcirc (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.vert a)
      (T.line.vert (a + 1)) (T.line.vert (a + 2))))

structure Fan48Concl (T : Track Γ G) (a b : ℤ) : Prop where
  subgraph : SubgraphProp T a b (H48 T a)
  inf_alpha : H48 T a ⊓ MulAction.stabilizer G (T.line.vert a) =
    Subgroup.normalizer (omega1 T.fixer : Set G) ⊓ MulAction.stabilizer G (T.line.vert a)
  inf_beta : H48 T a ⊓ MulAction.stabilizer G (T.line.vert (a + 1)) =
    Lcirc (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.vert a) (T.line.vert (a + 1))
      (T.line.vert (a + 2))
  normal : ∀ h ∈ H48 T a, ∀ z ∈ T.fixer, h * z * h⁻¹ ∈ T.fixer
  length : b - a ≤ 8
  central : ∀ x ∈ Subgroup.normalizer (omega1 T.fixer : Set G) ⊓
      MulAction.stabilizer G (T.line.vert a), orderOf x = 3 → ∀ z ∈ T.fixer, x * z = z * x
  swap : ∃ g ∈ Lcirc (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.vert a)
    (T.line.vert (a + 1)) (T.line.vert (a + 2)), g • T.line.vert a = T.line.vert (a + 2)

variable (T : Track Γ G) (a : ℤ)

theorem H48_le_normalizer : H48 T a ≤ Subgroup.normalizer (omega1 T.fixer : Set G) := by
  rw [H48, Subgroup.closure_le]
  rintro g (hg | hg)
  · exact hg.1
  · exact hg.1.1

theorem inf_le_H48 : Subgroup.normalizer (omega1 T.fixer : Set G) ⊓
    MulAction.stabilizer G (T.line.vert a) ≤ H48 T a := fun _ hg =>
  Subgroup.subset_closure (Or.inl hg)

theorem lcirc_le_H48 : Lcirc (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.vert a)
    (T.line.vert (a + 1)) (T.line.vert (a + 2)) ≤ H48 T a := fun _ hg =>
  Subgroup.subset_closure (Or.inr hg)

end CFSG.Quasithin.Fan86
