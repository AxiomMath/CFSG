module

public import CFSG.RankThree.PartOne.S12.Fusion
public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.RankThree.PartOne.S12.Sec1212

public section

namespace CFSG.RankThree.PartOne

@[expose] def Node12FusionRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → torusWeylHasPCore p E →
    (pCoreFixed p E = E ⊓ L ∧ Nat.card E = p * Nat.card ↥(E ⊓ L) ∧
      ¬ p ∣ Nat.card (Subgroup.center L)) →
    (Nonempty (↥(CFSG.pCore p ↥(torusWeyl E)) ≃* ↥(E ⊓ L)) ∧
      (∀ e e' : E, (e : G) ∉ L → (e' : G) ∉ L →
        ∃! φ : ↥(CFSG.pCore p ↥(torusWeyl E)),
          ∃ k : ℤ, ((φ : ↥(torusWeyl E)) : MulAut E) e = e' ^ k) ∧
      (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊔
        torusImage E (cNormalizer c) = torusWeyl E ∧
      (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊓
        torusImage E (cNormalizer c) = ⊥) →
    (¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) ∨ (p = 5 ∧ RowModel p L 12)) →
    ∃ P Q : Subgroup G, IsSylowOf p P ⊤ ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧
      (∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P) ∧ c ∈ P ∧ c ∉ Q ∧
      ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q

theorem node12Fusion_of_rest (hrest : Node12FusionRest) (h122 : Node122) (h122b : Node122b)
    (h123 : Node123) (h124 : Node124) (h125 : Node125) (h1210 : Node1210) (h1211 : Node1211)
    (h1212 : Node1212a) : Node12Fusion := by
  intro G _ _ p A c L E h hT hX
  exact hrest G p A c L E h (Sec12Facts.of_nodes h122 h122b h123 h124 h125 h) hT hX
    (h1210 G p A c L E h hT hX) (h1211 G p A c L E h hT hX) (h1212 G p A c L E h hT hX)

end CFSG.RankThree.PartOne
