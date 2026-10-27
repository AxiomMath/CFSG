module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Defs
public import CFSG.Assembly.InCatalog

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def T5Fus42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → (LocalOrthI B b₀ ∨ LocalOrthII B b₀) →
      Fus42 B b₀

@[expose] def T5ThmA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → LocalOrthII B b₀ → Fus42 B b₀ →
      OddCoreTrivial E → ∃ B' : Basis3 G (5 + 1), Adapted B' b₀ K E ∧ RecOutTwD5 B' b₀

@[expose] def T5Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    KProper InCatalog G → IsCharTwoType G →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → RecOutTwD5 B b₀ → Fus42 B b₀ →
      ∃ t : G, NineFourData B t

end CFSG.StandardType.FrameRoute.FS81

end
