module

public import CFSG.RankThree.PartOne.S12.Sec15Items

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def Node1512Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∀ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) →
      T ⊓ Subgroup.centralizer (lieGenerated p E : Set G) = ⊥

@[expose] def Node1513 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    (Outcome152Three p E A (lieGenerated p E) ∨ Outcome152Four p E A (lieGenerated p E)) →
    ∀ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) → T ≤ lieGenerated p E

@[expose] def LieRow1 {G : Type} [Group G] (p : ℕ) (I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ Nonempty (I ≃* projSL 4 (GaloisField 2 f))

@[expose] def LieRow2 {G : Type} [Group G] (p : ℕ) (I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ Nonempty (I ≃* projSp 3 (GaloisField 2 f))

@[expose] def LieRow3 {G : Type} [Group G] (p : ℕ) (I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
    ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (I ≃* projOmegaMinus 3 (GaloisField 2 f) b c)

@[expose] def LieRow4 {G : Type} [Group G] (p : ℕ) (I : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
    ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (I ≃* projOmegaMinus 3 (GaloisField 2 f) b c)

@[expose] def LieRow {G : Type} [Group G] (r p : ℕ) (I : Subgroup G) : Prop :=
  match r with
  | 1 => LieRow1 p I
  | 2 => LieRow2 p I
  | 3 => LieRow3 p I
  | 4 => LieRow4 p I
  | _ => False

structure Config1514 {G : Type} [Group G] (p : ℕ) (I H T A₀ : Subgroup G) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  le_H : I ≤ H
  H_le_N : H ≤ Subgroup.normalizer (I : Set G)
  faithful : H ⊓ Subgroup.centralizer (I : Set G) = ⊥
  sylow : IsSylowOf 2 T H
  A_le : A₀ ≤ I
  A_elem : IsElementaryAbelian p ↥A₀
  A_card : Nat.card ↥A₀ = p ^ 3

@[expose] def KF1513Row (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (I H T A₀ : Subgroup G),
    Config1514 p I H T A₀ → LieRow r p I → ¬ T ≤ I →
    ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ I ∧ I ⊓ Subgroup.centralizer ({t} : Set G) ≠ ⊥ ∧
      (∀ Q : Subgroup G, Q ≤ I ⊓ Subgroup.centralizer ({t} : Set G) →
        I ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Q : Set G) →
        IsPGroup 2 Q → Q = ⊥) ∧
      ∃ h ∈ H, ∃ B : Subgroup G, B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.centralizer ({t} : Set G)

@[expose] def KF1513 : Prop := ∀ r : ℕ, 3 ≤ r → r ≤ 4 → KF1513Row r

@[expose] def Node1514Even' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧
      (∃ n ∈ lieNormalizer p E, ∃ B₁ : Subgroup G, B₁ ≤ A ∧
        B₁.map (MulAut.conj n).toMonoidHom ≤
          (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
        Nat.card A ≤ p * Nat.card B₁) ∧
      (∃ x ∈ omegaOneCenterIn T, x ≠ 1 ∧
        ∃ n ∈ lieNormalizer p E, ∃ B₂ : Subgroup G, B₂ ≤ A ∧
        B₂.map (MulAut.conj n).toMonoidHom ≤
          (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer ({x} : Set G) ∧
        Nat.card A ≤ p * Nat.card B₂)

@[expose] def Node1514Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧
      A ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G) ∧
      ∃ B : Subgroup G, B ≤ E ∧
        B ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
        IsElementaryAbelian p B ∧ Nat.card B = p ^ 2

theorem node1514'_of_cases (hEven : Node1514Even') (hFive : Node1514Five) : Node1514' := by
  intro G _ _ p A c L E h15 hF hout
  by_cases hEA : E = A
  · obtain ⟨T, hT, hX, hY⟩ := hEven G p A c L E h15 hF hout hEA
    refine ⟨T, hT, fun _ => hX, fun _ => hY, fun h5 => ?_⟩
    obtain ⟨_, -, -, -, -, -, hne, -⟩ := h5
    exact absurd hEA hne
  · have hfive : Outcome152Five p E A (lieGenerated p E) := hout.five_of_ne hEA
    obtain ⟨T, hT, hY, hB⟩ := hFive G p A c L E h15 hF hfive
    exact ⟨T, hT, fun h => absurd h hEA, fun h => absurd h hEA, fun _ => ⟨hY, hB⟩⟩

end CFSG.RankThree.PartOne
