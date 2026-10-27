module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Pieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def T5Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → LocalOrthII B b₀ → Fus42 B b₀ →
      OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 5 →
          ∃ B' : Basis3 G (5 + 1), Adapted B' b₀ K E ∧ RecOutTwD5 B' b₀

@[expose] def T5Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → LocalOrthII B b₀ → Fus42 B b₀ →
      OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenFix0 5 → False

@[expose] def T5N0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → LocalOrthII B b₀ → Fus42 B b₀ →
      OddCoreTrivial E →
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 5 → False

theorem t5ThmA_of_cases (hM : T5Main) (hF : T5Fix) (hN : T5N0) : T5ThmA := by
  intro G _ _ b₀ K E hstd B hB hII hfus hodd
  rcases hII.2 with h | h | h
  · exact (hF G b₀ K E hstd B hB hII hfus hodd h).elim
  · exact (hN G b₀ K E hstd B hB hII hfus hodd h).elim
  · exact hM G b₀ K E hstd B hB hII hfus hodd h

end CFSG.StandardType.FrameRoute.FS81

end
