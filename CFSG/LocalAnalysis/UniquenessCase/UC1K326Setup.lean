module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.Defs
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.Blueprint (LieModel)

abbrev ZWr (n : ℕ) : Type := Multiplicative (ZMod (3 ^ n)) ≀ᵣ Multiplicative (ZMod 3)

@[expose] def jOf {G : Type} [Group G] (P : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.elemThompson K 3) P

@[expose] def z2Of {G : Type} [Group G] (P : Subgroup G) : Subgroup G :=
  (Subgroup.upperCentralSeries ↥P 2).map P.subtype

@[expose] def OmegaCentral {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∀ z : ↥P, z ∈ Subgroup.center ↥P → z ^ 3 = 1 → (z : G) ∈ Subgroup.center G

structure Hyp326 (G : Type) [Group G] [Finite G] (n : ℕ) (P : Subgroup G) : Prop where
  kgroup : CFSG.Open.IsKGroup G
  core : CFSG.pPrimeCore 3 G = ⊥
  one_le : 1 ≤ n
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤
  wr : Nonempty (↥P ≃* ZWr n)
  central : OmegaCentral P

@[expose] def K326P1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → CFSG.pPrimeCore 3 G = ⊥ →
    ∀ n : ℕ, 1 ≤ n → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
    Nonempty (↥P ≃* ZWr n) → OmegaCentral P →
    ∀ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤ →
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ CFSG.Open.IsQuasisimple ↥L ∧
          Nat.card (Subgroup.center ↥L) = 3 ∧ LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ CFSG.Open.IsQuasisimple ↥L ∧
          Nat.card (Subgroup.center ↥L) = 3 ∧ LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p f)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
