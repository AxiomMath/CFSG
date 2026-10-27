module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def L1N7Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.twD7 → ∀ B : Basis3 G (Row.twD7.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 Row.twD7.n →
          ∃ B' : Basis3 G (Row.twD7.n + 1), Adapted B' b₀ K E ∧ RecOut Row.twD7 B' b₀

@[expose] def L1N7Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.twD7 → ∀ B : Basis3 G (Row.twD7.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenFix0 Row.twD7.n →
          False

@[expose] def L1N7N0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E Row.twD7 → ∀ B : Basis3 G (Row.twD7.n + 1), Adapted B b₀ K E →
      LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 Row.twD7.n →
          False

theorem l1N7_of_cases (hM : L1N7Main) (hF : L1N7Fix) (hN : L1N7N0) : L1N7 := by
  intro G _ _ b₀ K E hstd B hB hII hfus hodd
  rcases hII.2 with h | h | h
  · exact (hF G b₀ K E hstd B hB hII hfus hodd h).elim
  · exact (hN G b₀ K E hstd B hB hII hfus hodd h).elim
  · exact hM G b₀ K E hstd B hB hII hfus hodd h

end CFSG.StandardType.FrameRoute.FS81
