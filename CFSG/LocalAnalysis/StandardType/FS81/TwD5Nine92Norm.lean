module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

@[expose] def T5Nine92Norm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    KProper InCatalog G → IsCharTwoType G →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → RecOutTwD5 B b₀ → Fus42 B b₀ →
    Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))) →
    ∀ g ∈ Subgroup.centralizer ({B.b 2} : Set G), ∀ x ∈ nineJ K (B.b 2),
      g * x * g⁻¹ ∈ nineJ K (B.b 2) ⊔ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G))

end CFSG.StandardType.FrameRoute.FS81

end
