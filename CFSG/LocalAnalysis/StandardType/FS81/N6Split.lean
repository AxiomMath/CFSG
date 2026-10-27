module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def L1N6Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 Row.D6.n →
          ∃ B' : Basis3 G (Row.D6.n + 1), Adapted B' b₀ K E ∧ RecOut Row.D6 B' b₀

@[expose] def L1N6Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.D6 → ∀ B : Basis3 G (Row.D6.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenFix0 Row.D6.n → False

end CFSG.StandardType.FrameRoute.FS81
