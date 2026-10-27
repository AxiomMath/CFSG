module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Track
public import CFSG.Quasithin.Recognition.Stroth.Str83G5Arith
public import CFSG.Quasithin.Background.OperatorJordanHolderJH1

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

structure IsChiEmb (ζ : GaloisField 2 n) (d₁ d₂ : G) (C S : Subgroup G) (φ : Coord n)
    (β : G → GaloisField 2 n) : Prop where
  map_mul : ∀ s ∈ S, ∀ t ∈ S, β (s * t) = β s + β t
  eq_zero_iff : ∀ s ∈ S, β s = 0 ↔ s ∈ C
  conj₁ : ∀ s ∈ S, β (d₁ * s * d₁⁻¹) = ζ ^ φ.1.val * β s
  conj₂ : ∀ s ∈ S, β (d₂ * s * d₂⁻¹) = ζ ^ φ.2.val * β s

@[expose] def chiLab (ζ : GaloisField 2 n) (d₁ d₂ : G) (C S : Subgroup G) : Set (Coord n) :=
  {φ | ∃ β, IsChiEmb ζ d₁ d₂ C S φ β}

@[expose] def clsSets (μ : Multiset (Coord n)) : Multiset (Set (Coord n)) :=
  μ.map fun φ => (cls φ : Set (Coord n))

structure Conf (G : Type) [Group G] (n : ℕ) where
  P₁ : Subgroup G
  P₂ : Subgroup G
  Q₁ : Subgroup G
  Q₂ : Subgroup G
  H : Subgroup G
  x₁ : G
  x₂ : G
  d₁ : G
  d₂ : G
  ζ : GaloisField 2 n
  k₀ : ZMod (2 ^ n - 1)
  m₀ : ZMod (2 ^ n - 1)
  odd : Odd n
  three_le : 3 ≤ n
  track : TrackData P₁ P₂ H x₁ x₂
  le_normalizer₁ : P₁ ≤ normalizer (Q₁ : Set G)
  le_normalizer₂ : P₂ ≤ normalizer (Q₂ : Set G)
  H_le₁ : H ≤ P₁
  H_le₂ : H ≤ P₂
  isPGroup₁ : IsPGroup 2 Q₁
  isPGroup₂ : IsPGroup 2 Q₂
  card₁ : Nat.card Q₁ = (2 ^ n) ^ 10
  card₂ : Nat.card Q₂ = (2 ^ n) ^ 11
  relIndex₁ : Q₁.relIndex Q₂ = (2 ^ n) ^ 2
  relIndex₂ : Q₂.relIndex Q₁ = 2 ^ n
  H_eq : H = zpowers d₁ ⊔ zpowers d₂
  commute : Commute d₁ d₂
  orderOf₁ : orderOf d₁ = 2 ^ n - 1
  orderOf₂ : orderOf d₂ = 2 ^ n - 1
  orderOf_ζ : orderOf ζ = 2 ^ n - 1
  conj₁₁ : x₁ * d₁ * x₁⁻¹ = d₁⁻¹
  conj₁₂ : x₁ * d₂ * x₁⁻¹ = d₁ ^ (-2 * m₀).val * d₂
  conj₂₂ : x₂ * d₂ * x₂⁻¹ = d₂⁻¹
  conj₂₁ : x₂ * d₁ * x₂⁻¹ = d₂ ^ (-2 * k₀).val * d₁
  isUnit_k₀ : IsUnit k₀
  isUnit_m₀ : IsUnit m₀
  baseS : ∀ m : ℕ, 1 ≤ m → ∃ d ≤ 2, dropS Q₁ Q₂ x₁ x₂ m = (2 ^ n) ^ d ∧
    ∃ l, IsYSeries H (win Q₁ Q₂ x₁ x₂ 0 m) l (win Q₁ Q₂ x₁ x₂ 1 m) ∧
      facMultiset (chiLab ζ d₁ d₂) l (win Q₁ Q₂ x₁ x₂ 1 m) =
        clsSets (Pattern.contrib k₀ m₀ (-1) 0 d)
  baseL : ∀ m : ℕ, 1 ≤ m → ∃ d ≤ 1, dropL Q₁ Q₂ x₁ x₂ m = (2 ^ n) ^ d ∧
    ∃ l, IsYSeries H (win Q₁ Q₂ x₁ x₂ (1 - m) 1) l (win Q₁ Q₂ x₁ x₂ (1 - m) 0) ∧
      facMultiset (chiLab ζ d₁ d₂) l (win Q₁ Q₂ x₁ x₂ (1 - m) 0) =
        clsSets (Pattern.contrib k₀ m₀ 1 1 d)
  fixA : ∀ δ ∈ zpowers d₁, δ ≠ 1 →
    Q₁ ⊓ centralizer ({δ} : Set G) = Q₁ ⊓ centralizer (zpowers d₁ : Set G)
  fixB : ∃ k : ℕ, (Q₁ ⊓ centralizer (zpowers d₁ : Set G)).relIndex Q₁ = (2 ^ n) ^ (4 * k)
  fixC : ∃ k : ℕ, (Q₁ ⊓ centralizer (H : Set G)).relIndex
    (Q₁ ⊓ centralizer (zpowers (d₁ ^ (-m₀).val * d₂) : Set G)) = (2 ^ n) ^ (4 * k)

end CFSG.Quasithin.Stroth.G5

end
