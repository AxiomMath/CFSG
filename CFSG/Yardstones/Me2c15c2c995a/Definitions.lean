module

public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual7

public section

namespace CFSG.Yardstones.Me2c15c2c995a

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Vocabulary

variable {G : Type} [Group G]

@[expose] def InCalV (M V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ V ≤ M ∧ M ≤ normalizer (V : Set G) ∧ CFSG.Open.IsElemAbelian 2 V

@[expose] def UniqueMaxLocal (M X : Subgroup G) : Prop :=
  X ≤ M ∧ ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → X ≤ H → H = M

@[expose] def InCalV1 (M T V : Subgroup G) : Prop :=
  InCalV M V ∧
    UniqueMaxLocal M (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G))

@[expose] def TwoReduced (M V : Subgroup G) : Prop :=
  ∀ K : Subgroup G, K ≤ M → M ≤ normalizer (K : Set G) → M ⊓ centralizer (V : Set G) ≤ K →
    (∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) →
      K ≤ centralizer (V : Set G)

@[expose] def InCalW (M T V : Subgroup G) : Prop :=
  InCalV1 M T V ∧ 8 ≤ Nat.card V ∧ TwoReduced M V

@[expose] def InCalWStar (M T V : Subgroup G) : Prop :=
  InCalW M T V ∧ ∀ W : Subgroup G, InCalW M T W → W ≤ V → W = V

@[expose] def InCalV0 (M V₀ V : Subgroup G) : Prop :=
  InCalV M V₀ ∧ InCalV M V ∧ V₀ ≤ V ∧ CFSG.CGT.Timmesfeld75.IsTI V₀ ∧
    ¬ CFSG.CGT.Timmesfeld75.IsTI V ∧
    (∀ v ∈ V, v ∉ V₀ → closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹} = V) ∧
    ¬ TwoReduced M V

@[expose] def CentralizersUnique (M T : Subgroup G) : Prop :=
  ∀ z ∈ T, (∀ t ∈ T, z * t = t * z) → z ≠ 1 →
    centralizer ({z} : Set G) ≤ M ∧
      ∀ g : G, g ∉ M → ¬ centralizer ({z} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom

@[expose] def Hyp123 (M T V₀ V : Subgroup G) : Prop :=
  (InCalWStar M T V ∧ V₀ = ⊥) ∨
    (InCalV0 M V₀ V ∧ CentralizersUnique M T ∧ ∀ W : Subgroup G, ¬ InCalW M T W)

@[expose] def CentralizesMod (V₀ V : Subgroup G) (m : G) : Prop :=
  ∀ v ∈ V, m * v * m⁻¹ * v⁻¹ ∈ V₀

@[expose] def centMod (V₀ V : Subgroup G) (m : G) : Set G :=
  {v | v ∈ V ∧ m * v * m⁻¹ * v⁻¹ ∈ V₀}

@[expose] def MBarGT3 (M V₀ V : Subgroup G) : Prop :=
  (∀ m ∈ M, ¬ CentralizesMod V₀ V m → CentralizesMod V₀ V (m * m) →
      16 * Nat.card (centMod V₀ V m) ≤ Nat.card V) ∧
    ((∀ m ∈ M, CentralizesMod V₀ V (m * m) → CentralizesMod V₀ V m) →
      16 * Nat.card V₀ ≤ Nat.card V)

end Vocabulary

@[expose] def Hyp125 {G : Type} [Group G] [Finite G] (S : Setup G) (V₀ V : Subgroup G) : Prop :=
  Hyp123 S.M S.T V₀ V ∧ ∃ H₀ ∈ hSet S.T S.M, Hyp124 S.M H₀

@[expose] def AGL81SectionFifteen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81Residual7NoU4 G

@[expose] def AGL81SectionSixteen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81Residual7U4 G

@[expose] def GF2nCatalogClause : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.IsKProper G → CFSG.IsCharacteristicPType G 2 →
    ∀ M : Subgroup G, CFSG.IsMaximalTwoLocal M →
    ∀ B : Subgroup G, Maximal (fun W : Subgroup G => W ≤ M ∧
      M ≤ normalizer (W : Set G) ∧ CFSG.Assembly.IsElemAbelian 2 W) B →
    CFSG.CGT.Timmesfeld75.IsTI B → CFSG.Blueprint.Catalog G

theorem gf2nCatalogClause_of_gf2nTypeStatement (h : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    GF2nCatalogClause :=
  fun G _ _ _ hnonab hK hchar M hM B hB hTI => (h G hnonab hK hchar M hM B hB hTI).2

@[expose] def AscTwelveEightEmptyW : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ S : Setup G, S.InMSigma → (∃ H₀ ∈ hSet S.T S.M, Hyp124 S.M H₀) →
      (∀ W : Subgroup G, ¬ InCalW S.M S.T W) →
      ∃ V₀ V : Subgroup G, InCalV0 S.M V₀ V ∧ CentralizersUnique S.M S.T

@[expose] def AscSixteenSixtyNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ S : Setup G, S.InMSigma → ∀ V₀ V : Subgroup G, Hyp125 S V₀ V →
      Nat.card V₀ ≤ 4 → MBarGT3 S.M V₀ V

@[expose] def AscEighteenTwentyFourConditional : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ S : Setup G, S.InMSigma → ∀ V₀ V : Subgroup G, Hyp125 S V₀ V →
      Nat.card V₀ ≤ 2 → MBarGT3 S.M V₀ V → False

@[expose] def AscSectionNineteenConditional : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ S : Setup G, S.InMSigma → ∀ V₀ V : Subgroup G, Hyp125 S V₀ V →
      2 < Nat.card V₀ → (Nat.card V₀ ≤ 4 → MBarGT3 S.M V₀ V) → False

@[expose] def AscEighteenTwentyFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ S : Setup G, S.InMSigma → ∀ V₀ V : Subgroup G, Hyp125 S V₀ V →
      2 < Nat.card V₀

@[expose] def AscSectionNineteen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ S : Setup G, S.InMSigma → ∀ V₀ V : Subgroup G, Hyp125 S V₀ V → False

@[expose] def AscTwentyTwoNineteen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → NotTIStage1930 G

@[expose] def AscSectionTwentyThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → TIStage1930 G

end CFSG.Yardstones.Me2c15c2c995a
