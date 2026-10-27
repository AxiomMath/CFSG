module

public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open

section Modules

variable {V : Type*} [CommGroup V]

@[expose] def I16Module (Gm : Subgroup (MulAut V)) (U Z : Subgroup V) (d : ℕ) : Prop :=
  (∃ m : ℕ, (m = 5 ∨ m = 7) ∧ d = 0 ∧ AlternatingNatural Gm U Z m) ∨
    (∃ m : ℕ, (m = 6 ∨ m = 8) ∧ d = 1 ∧ AlternatingNatural Gm U Z m) ∨
    (∃ a : ℕ, 1 < a ∧ d = a ∧ BinaryNaturalSL Gm U Z 2 a) ∨
    (∃ a : ℕ, 1 ≤ a ∧ d = 0 ∧ BinaryOrthogonalFour Gm U Z a) ∨
    (∃ a : ℕ, 1 < a ∧ d = 0 ∧ BinaryNaturalSL Gm U Z 3 a) ∨ (d = 1 ∧ BinaryNaturalSL Gm U Z 3 1) ∨
    (∃ a : ℕ, 1 < a ∧ d = a ∧ BinaryNaturalSp4 Gm U Z a) ∨
    (∃ a : ℕ, 1 ≤ a ∧ d = a ∧ G2NaturalDerived Gm U Z a) ∨
    (∃ m : ℕ, (m = 4 ∨ m = 5) ∧ d = 0 ∧ BinaryNaturalSL Gm U Z m 1) ∨
    (d = 0 ∧ SLExteriorTwo Gm U Z 5) ∨ (d = 0 ∧ A7Four Gm U Z) ∨ (d = 0 ∧ TripleA6Six Gm U Z)

end Modules

@[expose] def AS_I_1_6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Gm : Subgroup (MulAut W)) (d : ℕ),
      (commV Gm = ⊤ → I16Module Gm ⊤ (fixV Gm) d → Nat.card (fixV Gm) ≤ 2 ^ d) ∧
      (fixV Gm = ⊥ → I16Module Gm (commV Gm) ⊥ d → (commV Gm).index ≤ 2 ^ d)

section TIPairs

variable {G : Type*} [Group G]

abbrev tiU (V A : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.normalizer (A : Set G)

abbrev tiB (V A : Subgroup G) : Subgroup G :=
  A ⊓ Subgroup.normalizer (V : Set G)

abbrev tiY (V A : Subgroup G) : Subgroup G :=
  tiU V A ⊔ tiB V A

abbrev tiX (V A : Subgroup G) : Subgroup G :=
  V ⊔ A

end TIPairs

@[expose] def AS_I_6_2_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V A : Subgroup G), IsElemAbelian 2 V → IsElemAbelian 2 A →
    Nat.card V = Nat.card A → IsTISetIn V ⊤ → IsTISetIn A ⊤ →
    (∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥) →
    tiU V A ≠ ⊥ → tiU V A < V →
      (tiU V A ⊓ tiB V A = ⊥ ∧ ⁅tiU V A, tiB V A⁆ = ⊥ ∧
        tiX V A ≤ Subgroup.normalizer (tiY V A : Set G) ∧
        ∀ v ∈ V, v ∉ tiU V A →
          tiU V A = tiY V A ⊓ Subgroup.centralizer ({v} : Set G) ∧
            tiU V A = ⁅tiY V A, Subgroup.zpowers v⁆) ∧
      ∃ _ : ((tiY V A).subgroupOf (tiX V A)).Normal,
        ((∃ m : ℕ, Odd m ∧
            Nonempty (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A) ≃* DihedralGroup m)) ∨
          (∃ n : ℕ, IsPSL 2 2 n (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A))) ∨
          ∃ n : ℕ, IsSz n (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A))) ∧
        Nat.card ↥((V.subgroupOf (tiX V A)).map
            (QuotientGroup.mk' ((tiY V A).subgroupOf (tiX V A)))) =
          2 ^ CFSG.pRank 2 (↥(tiX V A) ⧸ (tiY V A).subgroupOf (tiX V A))

end CFSG.Quasithin.ASInputs
