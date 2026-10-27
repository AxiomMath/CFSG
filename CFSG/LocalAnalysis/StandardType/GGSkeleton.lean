module

public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.Adapters.ClassicalCatalogReverse

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def ggG0 (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) :
    Subgroup G :=
  L ⊔ ⨆ (y : G) (K : Subgroup G) (_ : LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J), K

@[expose] def GGSixHyp (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  (B ≤ Bs ∧ IsElemAbelian p Bs ∧ Nat.card Bs = p ^ pRank p (⊤ : Subgroup G)) ∧
    LargeEvenStdSub p B x L D J ∧
    LargeEvenMarking (ggG0 p B x L D J) (fun _ _ _ I _ θ =>
      Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end Defs

@[expose] def GGHoltAt {G : Type} [Group G] (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ ∃ r : G, orderOf r = 2 ∧ (∀ q : G ⧸ M, r • q = q ↔ q = ((1 : G) : G ⧸ M)) ∧
    ∃ T : Sylow 2 M, r ∈ (T : Subgroup M).map M.subtype ∧
      (T : Subgroup M).map M.subtype ≤ Subgroup.centralizer {r}

@[expose] def GGSecOneFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∃ Bs D J : Subgroup G, GGSixHyp p B Bs x L D J

@[expose] def GGSecSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → 4 ≤ evenRank G → ∀ p : ℕ, p ∈ LargeEvenBeta 4 G →
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), LargeEvenSStar p B x L →
      LargeEvenStandardType p B x L → ∀ Bs D J : Subgroup G, GGSixHyp p B Bs x L D J →
        Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
          GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))

theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : InCatalog Y) :
    InCatalog X :=
  CFSG.Assembly.inCatalog_isoInvariant e h

theorem ne_bot_of_isComponentOf' {G : Type} [Group G] {L K : Subgroup G} (hL : IsComponentOf L K) :
    L ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, -, hsimp⟩ := hL
  obtain ⟨a, b, hab⟩ := hsimp.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp a.2)
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.mp b.2)
      rw [ha, hb]

section Closing


theorem inCatalog_of_lieModel_std (X : Type) [Group X] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : LieModel X t n p f) : InCatalog X := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact ClassicalModels.inCatalog_of_statedClassicalModel X t n p f h
  · exact TauCetiBridge.exceptionalRep_inCatalog X (.inl ⟨t, p, f, ht, h⟩)
  · exact TauCetiBridge.exceptionalRep_inCatalog X (.inr (.inl ⟨t, p, f, ht, h⟩))
  · exact TauCetiBridge.exceptionalRep_inCatalog X (.inr (.inr ⟨p, f, h⟩))


theorem inCatalog_of_ggSix (hHolt : HoltUniqueFixedPointSimple) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hL : L ≠ ⊥) (h6 : GGSixHyp p B Bs x L D J)
    (hM : Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
      GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))) :
    InCatalog G := by
  rcases hM with hM | ⟨hne, r, hr, hfix, hT⟩
  · obtain ⟨-, -, hmark, -, -⟩ := h6
    have hN : (ggG0 p B x L D J).Normal := Subgroup.normalizer_eq_top_iff.mp hM
    have htop : ggG0 p B x L D J = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ggG0 p B x L D J) with h | h
      · exact absurd (le_bot_iff.mp (h ▸ (le_sup_left : L ≤ ggG0 p B x L D J))) hL
      · exact h
    obtain ⟨lab, -, hm⟩ := largeEvenMarking_markedModel_centerQuot hmark
    have hc : InCatalog (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) :=
      inCatalog_of_lieModel_std _ hm
    have hZ : Subgroup.center ↥(ggG0 p B x L D J) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzG : (z : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ ggG0 p B x L D J := htop ▸ Subgroup.mem_top g
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
      rw [center_eq_bot_of_simple hnonab, Subgroup.mem_bot] at hzG
      exact Subgroup.mem_bot.mpr (Subtype.ext hzG)
    have e1 : G ≃* ↥(ggG0 p B x L D J) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    have e2 : ↥(ggG0 p B x L D J) ≃*
        ↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact inCatalog_of_mulEquiv (e1.trans e2) hc
  · exact inCatalog_of_unique_fixed hHolt hnonab hne hr hfix hT

theorem lc_gl_std_of_inputs (hHolt : HoltUniqueFixedPointSimple) (h15 : GGSecOneFiveInput)
    (h6 : GGSecSixInput) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G := by
  obtain ⟨Bs, D, J, hsix⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  have hL : L ≠ ⊥ := ne_bot_of_isComponentOf' hS.2.2.2.1
  exact inCatalog_of_ggSix hHolt hnonab hL hsix
    (h6 G hnonab hK hchar he p hp B x L hS hst Bs D J hsix)

end Closing

end CFSG.StandardType
