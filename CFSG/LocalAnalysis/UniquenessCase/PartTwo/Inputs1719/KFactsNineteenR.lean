module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)

@[expose] def K_19_glue4_torus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 3 ≤ n →
    (IsSp4 X n ∨ IsL2Square X n ∨ IsSzSquare X n ∨ S17.IsL2U3Product X n) →
    ∀ U : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ →
      ∃ (A₁ : Subgroup X) (t : X), A₁ ≤ normalizer (U : Set X) ∧ IsZModSq A₁ n ∧
        (∀ x ∈ normalizer (U : Set X), x ^ (2 ^ n - 1) ∈ U ↔ x ∈ A₁ ⊔ U) ∧
        (∃ k : ℕ, orderOf t = 2 ^ k) ∧ ∀ a ∈ A₁, t * a * t⁻¹ = a⁻¹

@[expose] def Shape19_16_124 (X : Type) [Group X] (Y : Subgroup X) : Prop :=
  (IsAlt X 10 ∧ (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin 6)))) ∨
  (IsA6ModZ3 X ∧ Y.index = 15) ∨
  (∃ m : ℕ, (m = 3 ∨ m = 4) ∧
    ((∃ ε : Bool, IsOmegaEps2 X ε m ∧ IsCentralizerOfTransvectionIn X m Y) ∨
      (IsAlt X (2 * m + 2) ∧
        ∃ (e : X ≃* alternatingGroup (Fin (2 * m + 2))) (a b : Fin (2 * m + 2)), a ≠ b ∧
          Y.map e.toMonoidHom =
            (Subgroup.centralizer
              ({Equiv.swap a b} : Set (Equiv.Perm (Fin (2 * m + 2))))).comap
              (alternatingGroup (Fin (2 * m + 2))).subtype)))

@[expose] def K_19_18_minNormal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), Shape19_16_124 X Y →
    ∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)

@[expose] def W10_4_9 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Kb Tb : Subgroup Y), Kb.Normal → IsSimpleGroup ↥Kb →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsChev ↥Kb q) →
    IsElemAbelian 2 Tb → 4 ≤ Nat.card Tb → Tb ⊓ centralizer (Kb : Set Y) = ⊥ →
    Kb ⊔ Tb = ⊤ → CFSG.CGT.Timmesfeld75.IsTI Tb →
    Nat.card Kb = 60 ∨ Nat.card Kb = 168 ∨ Nat.card Kb = 360

@[expose] def K_19_glue7_L2small : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Kb : Subgroup Y), Kb.Normal → IsSimpleGroup ↥Kb →
    centralizer (Kb : Set Y) = ⊥ → (Nat.card Kb = 60 ∨ Nat.card Kb = 168 ∨ Nat.card Kb = 360) →
    ∀ e v : Y, (orderOf e).Prime → 7 ≤ orderOf e → orderOf v = 2 → e * v = v * e → False

@[expose] def K_19_JRgen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Kb : Subgroup Y), Kb.Normal → IsSimpleGroup ↥Kb →
    centralizer (Kb : Set Y) = ⊥ → CFSG.Open.IsCatalogGroup ↥Kb →
    CFSG.LocalAnalysis.UniquenessCase.UC22.F10.IsJankoReeType10 ↥Kb →
    ∀ v₁ v₂ : Y, orderOf v₁ = 2 → orderOf v₂ = 2 → v₁ ≠ v₂ → v₁ * v₂ = v₂ * v₁ →
      Kb ≤ (Kb ⊓ centralizer ({v₁} : Set Y)) ⊔ (Kb ⊓ centralizer ({v₂} : Set Y))

@[expose] def W7_9_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    IsSimpleGroup G → CFSG.Open.IsCharTwoType G → CFSG.Open.IsKProper G →
    ∀ (M I X Y H : Subgroup G),
      rankThreeIsMaxTwoLocal M →
      I ≤ M → (I.subgroupOf M).Normal →
      X ≤ M → S17.oUpperTwo X ≤ I →
      (∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → X ≤ normalizer (R : Set G) →
        pCoreOf 2 I ≤ R → calMOf (M ⊓ normalizer (R : Set G)) = {M}) →
      Y ≤ M → Y = X ⊔ pCoreOf 2 Y → pCoreOf 2 Y ≠ ⊥ → calMOf Y ≠ {M} →
      (∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
        calMOf Z ≠ {M} → Y ≤ Z → Z = Y) →
      Y ≤ H → ¬ H ≤ M → pCoreOf 2 H ≠ ⊥ →
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P → Y ≤ normalizer (P : Set G) → P ≤ pCoreOf 2 Y

@[expose] def W7_9_4c : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    IsSimpleGroup G → CFSG.Open.IsCharTwoType G → CFSG.Open.IsKProper G →
    ∀ (M I X Y L H : Subgroup G),
      rankThreeIsMaxTwoLocal M →
      I ≤ M → (I.subgroupOf M).Normal →
      X ≤ M → S17.oUpperTwo X ≤ I →
      (∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → X ≤ normalizer (R : Set G) →
        pCoreOf 2 I ≤ R → calMOf (M ⊓ normalizer (R : Set G)) = {M}) →
      Y ≤ M → Y = X ⊔ pCoreOf 2 Y → pCoreOf 2 Y ≠ ⊥ → calMOf Y ≠ {M} →
      (∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
        calMOf Z ≠ {M} → Y ≤ Z → Z = Y) →
      Y ≤ H → ¬ H ≤ M → pCoreOf 2 H ≠ ⊥ →
      H = L ⊔ Y → L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 H) →
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsComponentModO2 H (L ⊔ pCoreOf 2 H) →
      ¬ CFSG.RankThree.PartOne.IsBlockInX (L.subgroupOf H) →
      ¬ ⁅Opp 2 (M ⊓ L), S17.oUpperTwo X⁆ ≤ pCoreOf 2 (Opp 2 (M ⊓ L)) ∧
        ⁅Opp 2 (M ⊓ L), S17.oUpperTwo X⁆ ≤ I

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
