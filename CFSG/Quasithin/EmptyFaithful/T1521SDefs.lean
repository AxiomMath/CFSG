module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def borelJoin1521 (S L : Subgroup G) : Subgroup G :=
  conjJoin S (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))

structure Std1521 (X S L : Subgroup G) : Prop where
  sqtk : IsSQTKIn X
  sylow : IsSylowTwoOf S X
  comp : L ∈ cComp X
  sylowL : IsSylowTwoOf (S ⊓ L) L
  not_norm : ¬ L ≤ Subgroup.normalizer (thompsonJ S : Set G)

@[expose] def CentralMoving1521 (S L : Subgroup G) : Prop :=
  ∃ z ∈ S, (∀ s ∈ S, z * s = s * z) ∧ ∃ l ∈ L, z * l ≠ l * z

@[expose] def Nrm1521 (S L : Subgroup G) : Prop :=
  ∃ B₀ : Subgroup G, B₀ ≤ borelJoin1521 S L ∧ B₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) ∧
    oTwoUpper B₀ = B₀ ∧
    ∀ v ∈ S, v ∈ Subgroup.normalizer (L : Set G) → (∀ b ∈ B₀, v * b = b * v) →
      ∀ l ∈ L, v * l = l * v

@[expose] def Exc1521 (X S L : Subgroup G) : Prop :=
  ∀ (p : ℕ) (Y : Subgroup G), (p = 3 ∨ p = 5) → Y ≤ X →
    Y ≤ Subgroup.normalizer (thompsonJ S : Set G) → Y ≤ Subgroup.normalizer (conjJoin S L : Set G) →
    IsPGroup p ↥Y → ((S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G)) → ⁅L, Y⁆ = ⊥

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Dich1521BlockL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    ⁅L, thompsonJ S⁆ = L → CharTwo L → IsBlock2 X L → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
    Nrm1521 S L ∨ Exc1521 X S L

@[expose] def Dich1521BlockA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    ⁅L, thompsonJ S⁆ = L → CharTwo L → IsBlock2 X L → IsAltType L 5 →
    Nrm1521 S L ∨ Exc1521 X S L

@[expose] def Dich1521L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n ↥L) → Nrm1521 S L ∨ Exc1521 X S L

@[expose] def Dich1521Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    ((∃ e : ℕ, IsSz e ↥L) ∨ IsSz 3 (↥L ⧸ CFSG.pCore 2 ↥L)) → Nrm1521 S L ∨ Exc1521 X S L

@[expose] def Dich1521U3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 2 ≤ n ∧ IsPSU 3 2 n ↥L) → Nrm1521 S L ∨ Exc1521 X S L

@[expose] def Dich1521L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L → CentralMoving1521 S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    ((∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) ∨ IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    Nrm1521 S L ∨ Exc1521 X S L

@[expose] def Dich1521Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) → Nrm1521 S L ∨ Exc1521 X S L

end CFSG.Quasithin
