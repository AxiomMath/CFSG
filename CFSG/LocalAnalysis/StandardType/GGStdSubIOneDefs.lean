module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Marked

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixHypI1 (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  GGSixHyp p B Bs x L D J ∧ Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

end Marked

@[expose] def GGSecOneFiveI1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∃ Bs D J : Subgroup G, GGSixHypI1 p B Bs x L D J

@[expose] def GGSecSixI1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∀ Bs D J : Subgroup G, GGSixHypI1 p B Bs x L D J →
        Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
          GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))

theorem ggSecOneFiveInput_of_i1 (h : GGSecOneFiveI1Input) : GGSecOneFiveInput := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst
  obtain ⟨Bs, D, J, h6, -⟩ := h G hnonab hK hchar he p hp B x L hS hst
  exact ⟨Bs, D, J, h6⟩

theorem ggSecSixI1Input_of_ggSecSixInput (h : GGSecSixInput) : GGSecSixI1Input :=
  fun G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J h6 =>
    h G hnonab hK hchar he p hp B x L hS hst Bs D J h6.1

section Closing


theorem lc_gl_std_of_i1_inputs (hHolt : HoltUniqueFixedPointSimple) (h15 : GGSecOneFiveI1Input)
    (h6 : GGSecSixI1Input) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G := by
  obtain ⟨Bs, D, J, hsix⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  exact inCatalog_of_ggSix hHolt hnonab (ne_bot_of_isComponentOf' hS.2.2.2.1) hsix.1
    (h6 G hnonab hK hchar he p hp B x L hS hst Bs D J hsix)

end Closing

section Genuine

@[expose] def GGSixHypV2I1 {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  GGSixHypV2 p B Bs x L D J ∧ Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

@[expose] def GGSecOneFiveV2I1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∃ Bs D J : Subgroup G, GGSixHypV2I1 p B Bs x L D J

@[expose] def GGSecSixV2I1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∀ Bs D J : Subgroup G,
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ →
        Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
        Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
          GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))

theorem ggSecOneFiveV2Input_of_v2I1 (h : GGSecOneFiveV2I1Input) : GGSecOneFiveV2Input := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst
  obtain ⟨Bs, D, J, h6, -⟩ := h G hnonab hK hchar he p hp B x L hS hst
  exact ⟨Bs, D, J, h6⟩

theorem ggSecSixV2I1Input_of_v2 (h : GGSecSixV2Input) : GGSecSixV2I1Input :=
  fun G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ h6 _ =>
    h G hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ h6

theorem ggSecOneFiveI1Input_of_v2I1 (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (ha' : GGBstarRankInput) (h15 : GGSecOneFiveV2I1Input) : GGSecOneFiveI1Input := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst
  obtain ⟨Bs, D, J, h, hI1⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  exact ⟨Bs, D, J,
    ggSixHyp_of_v2 hR1 hR ha' ⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst⟩ h, hI1⟩

theorem ggSecSixV2I1Input_of_i1 (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (ha' : GGBstarRankInput) (h6 : GGSecSixI1Input) : GGSecSixV2I1Input := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ h hI1
  exact h6 G hnonab hK hchar he p hp B x L hS hst Bs D J
    ⟨ggSixHyp_of_v2Core hR1 hR ha' ⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst⟩ h, hI1⟩

end Genuine

section Skeleton

theorem lc_gl_std_of_v2I1_inputs (hHolt : HoltUniqueFixedPointSimple)
    (h15 : GGSecOneFiveV2I1Input) (h6 : GGSecSixV2I1Input) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G)
    (B : Subgroup G) (x : G) (L : Subgroup G) (hS : LargeEvenSStar p B x L)
    (hst : LargeEvenStandardType p B x L) : InCatalog G := by
  obtain ⟨Bs, D, J, ⟨t, n, f, ψ, hsix⟩, hI1⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  exact inCatalog_of_ggSixV2Core hHolt hnonab (ne_bot_of_isComponentOf' hS.2.2.2.1) hsix
    (h6 G hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ hsix hI1)

end Skeleton

end CFSG.StandardType
