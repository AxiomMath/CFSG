module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineOdd
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineInvol
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineHyp

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

@[expose] def T5NineO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
    KProper InCatalog G → IsCharTwoType G →
    ∀ B : Basis3 G (5 + 1), Adapted B b₀ K E → RecOutTwD5 B b₀ → Fus42 B b₀ →
    Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))) →
    ∀ t : G, orderOf t = 2 → t * B.b 0 * t⁻¹ = (B.b 0)⁻¹ → t * B.b 1 * t⁻¹ = (B.b 1)⁻¹ →
      (∀ j : Fin (5 + 1), 2 ≤ j.val → t * B.b j = B.b j * t) →
      ∀ Q : Subgroup G, IsPGroup 2 Q →
        Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G) →
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G) ≤
          Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.zpowers t

theorem t5Nine_of_o2 (h : T5NineO2) : T5Nine := by
  intro G _ _ b₀ K E hstd hK hchar B hB hrec hfus
  have hD := odd_card_centralizer_inf_of_isCharTwoType hstd hchar hB hrec hfus
  have hodd := odd_card_centralizer_span_of_odd hstd hB hrec hD
  obtain ⟨t, ht, ht0, ht1, ht2⟩ := exists_nineInvol_of_recOutTwD5 hB hrec hodd
  exact ⟨t, ht, ht0, ht1, ht2, h G b₀ K E hstd hK hchar B hB hrec hfus hodd t ht ht0 ht1 ht2,
    exists_centralizer_conj_mem_hyperplane_of_recOutTwD5 hB hrec hfus hodd ht ht0 ht1 ht2⟩

end CFSG.StandardType.FrameRoute.FS81

end
