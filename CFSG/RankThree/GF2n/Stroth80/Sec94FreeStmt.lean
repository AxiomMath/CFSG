module

public import CFSG.RankThree.GF2n.Stroth80.Sec94End
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RSec4

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def Step94CNAllStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) → 5 ≤ n →
      ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q → hc.CN u ≤ Y

@[expose] def Step94EndFreeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    (∃ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q ∧
        QuotSat Y Q (IsSLModel 2 (Nat.card Z))) → False

theorem step94EndFree_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h92 : Stroth92Statement) (hB : Step94ConjVStatement) (hall : Step94CNAllStatement) :
    Step94EndFreeStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj ⟨Y, hdp, hYsl⟩
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  obtain ⟨u, huLY, huQ⟩ :=
    HS9.exists_mem_LB_inf_Y_not_mem hc (sec4_of h34 h311a G M Q Z B hc n t hs _ Y hsplit)
  have hn5 := sec9NGeFive_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs
  have hCN :=
    hall G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u huLY huQ
  have huL : u ∈ LB M Q B := (Subgroup.mem_inf.mp huLY).1
  have hle := HS9.card_CN_le_of_le_Y h34 h311a hs hsplit huL huQ hCN
  exact absurd (hs.large u huL huQ) (not_lt.mpr hle)

theorem step94NSix_of_free (hE : Step94EndFreeStatement) : Step94NSixStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj hY
  exact (hE G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj hY).elim

theorem step94End_of_free (hE : Step94EndFreeStatement) : Step94EndStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj hY _
  exact hE G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj hY

@[expose] def Step94PointStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ m ∈ M, LB M Q (conjSubgroup m B) ≤ Rt M (LB M Q B) t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m (LB M Q B) = conjSubgroup r (LB M Q B)

@[expose] def Step94ZInR0Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) → 5 ≤ n →
      ∀ z ∈ M, conjSubgroup z Z0 ≤ LB M Q B → conjSubgroup z Z0 ≤ Sec9R0 hc t x

@[expose] def Step94YConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) →
      ∀ z ∈ M, conjSubgroup z Z0 ≤ LB M Q B → conjSubgroup z Y = Y

@[expose] def Step94GenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) → 5 ≤ n →
      ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q →
        ∃ c ∈ M, ∃ d ∈ M,
          LB M Q (conjSubgroup c B) ⊔ LB M Q (conjSubgroup d B) ≤ Rt M (LB M Q B) u ∧
          (∀ r ∈ Rt M (LB M Q B) u, ∃ y ∈ LB M Q (conjSubgroup c B) ⊔ LB M Q (conjSubgroup d B),
            y⁻¹ * r ∈ hc.CN u) ∧
          (∀ y ∈ LB M Q (conjSubgroup c B) ⊔ LB M Q (conjSubgroup d B),
            ∀ w ∈ LB M Q B ⊓ Y, ⁅y, w⁆ ∈ Q)

@[expose] def Step94CountNuStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) → 5 ≤ n →
      ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q → Nat.card ↥(LB M Q B ⊓ hc.CN u) ≤ Nat.card Q * Nat.card Z

@[expose] def Step94SNuStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) → 5 ≤ n →
      ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q → LB M Q B ⊓ Y ≤ hc.CN u

@[expose] def Step94NotQBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    ∀ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q →
      QuotSat Y Q (IsSLModel 2 (Nat.card Z)) → 5 ≤ n →
      ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q → ¬ Vt M (LB M Q B) B Z u ≤ QB B

@[expose] def Step94CYWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → 5 ≤ n →
    ∀ y ∈ Y, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, w⁆ ∈ Vt M (LB M Q B) B Z t) → y ∈ Q

@[expose] def Step94DimQStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y →
    ∀ u ∈ LB M Q B ⊓ Y, u ∉ Q →
      Nat.card Z ^ (n + 1) ≤ Nat.card ↥(⁅Q, Subgroup.zpowers u⁆ ⊔ Z)

end CFSG.RankThree.GF2n.Stroth80
