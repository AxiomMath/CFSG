module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

@[expose] def FactL2Offender : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (Hs Gm P : Subgroup (MulAut U)) (e : ℕ), 4 ≤ e →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
      Nonempty (↥Gm ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsPGroup 2 ↥P → P ≤ Subgroup.normalizer (Gm : Set (MulAut U)) → Gm ⊔ P = Hs →
    pCoreOf 2 Hs = ⊥ →
    ∀ A ∈ E3.aSet e Hs, A ≤ Gm ∧ IsSylowTwoOf A Gm ∧ Nat.card ↥A = 2 ^ e

@[expose] def FactL2NatRank : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (Gm R : Subgroup (MulAut U)) (e : ℕ), 1 < e →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
      Nonempty (↥Gm ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsSylowTwoOf R Gm →
    ∀ (s : ℕ) (W : Fin s → Subgroup U), (∀ i, fixV Gm ≤ W i) →
      (∀ i, W i ⊓ (fixV Gm ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j) = fixV Gm) →
      (fixV Gm ⊔ ⨆ i, W i) = ⊤ → (∀ i, BinaryNaturalSL Gm (W i) (fixV Gm) 2 e) →
        rkIdx (fixV R) = s * e

@[expose] def FactL2Orth : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (Gm R : Subgroup (MulAut U)) (e : ℕ), 1 < e →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
      Nonempty (↥Gm ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsSylowTwoOf R Gm → BinaryNaturalSL Gm ⊤ (fixV Gm) 2 e →
    Nat.card ↥(commV R) = 2 ^ (2 * e) →
      ∀ a ∈ R, ∀ b ∈ R, a ≠ 1 → b ≠ 1 → a ≠ b →
        commV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers b) = ⊥

structure FactsL2 : Prop where
  offender : FactL2Offender
  natRank : FactL2NatRank
  orth : FactL2Orth

end CFSG.Quasithin.Vol2.Ch11.SecB
