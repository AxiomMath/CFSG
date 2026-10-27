module

public import CFSG.Quasithin.EmptyFaithful.T1521SJ
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def E1L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) → thompsonJ S ≤ innerPart1521 S L

@[expose] def E1Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) → thompsonJ S ≤ innerPart1521 S L

@[expose] def AutFactL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) →
    ((∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) ∨ IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    IsSylowTwoOf P L → ∀ v ∈ Subgroup.normalizer (L : Set G), IsPGroup 2 ↥(Subgroup.zpowers v) →
      (∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) →
      ∀ l ∈ L, v * l = l * v

@[expose] def AutFactSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) → (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) →
    IsSylowTwoOf P L → ∀ v ∈ Subgroup.normalizer (L : Set G), IsPGroup 2 ↥(Subgroup.zpowers v) →
      (∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) →
      ∀ l ∈ L, v * l = l * v

theorem dich1521Sp4_of (hE : E1Sp4) (hA : AutFactSp4) : Dich1521Sp4 := by
  intro G _ _ X S L hStd hco hZ hty
  refine Or.inl (nrm1521_of_inner (hE G X S L hStd hco hZ hty) ?_)
  intro v hvS hvN hc l hl
  exact hA G L (S ⊓ L) hco.2.2 hZ hty hStd.sylowL v hvN
    (hStd.sylow.2.1.to_le (Subgroup.zpowers_le.mpr hvS)) hc l hl

@[expose] def Nrm1521U3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 2 ≤ n ∧ IsPSU 3 2 n ↥L) → Nrm1521 S L

theorem dich1521U3_of (h : Nrm1521U3) : Dich1521U3 := by
  intro G _ _ X S L hStd hco hZ hty
  exact Or.inl (h G X S L hStd hco hZ hty)

end CFSG.Quasithin
