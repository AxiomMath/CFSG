module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Defs

variable {S : Type} [Group S]

@[expose] def omegaCenter (P : Subgroup S) : Subgroup S where
  carrier := {z | z ∈ P ∧ (∀ y ∈ P, z * y = y * z) ∧ z * z = 1}
  one_mem' := ⟨P.one_mem, fun y _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haP, hac, ha2⟩ ⟨hbP, hbc, hb2⟩
    refine ⟨P.mul_mem haP hbP, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hac b hbP]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haP, hac, ha2⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hinv]
    exact ⟨haP, hac, ha2⟩

theorem mem_omegaCenter {P : Subgroup S} {z : S} :
    z ∈ omegaCenter P ↔ z ∈ P ∧ (∀ y ∈ P, z * y = y * z) ∧ z * z = 1 := Iff.rfl

end Defs

section Data

variable {S : Type} [Group S]

structure E68RankOneData (P : Subgroup S) (n : ℕ) : Prop where
  centralizer_le : ∀ y : S, (∀ p ∈ P, y * p = p * y) → y ∈ P
  quot_comm : ∀ a ∈ Subgroup.normalizer (P : Set S), ∀ b ∈ Subgroup.normalizer (P : Set S),
    a * b * a⁻¹ * b⁻¹ ∈ P
  order_three : ∀ c ∈ Subgroup.normalizer (P : Set S), orderOf c = 3 →
    4 < (P ⊓ Subgroup.centralizer ({c} : Set S)).relIndex P ∨
      (Nat.card P = 4 ∧ P ⊓ Subgroup.centralizer ({c} : Set S) = ⊥)
  card_root : Nat.card (omegaCenter P) = 2 ^ n
  singer : ∃ x ∈ Subgroup.normalizer (P : Set S), ∀ z ∈ omegaCenter P, z ≠ 1 →
    ∀ w ∈ omegaCenter P, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w
  bender : ∀ Y : Subgroup S, P ≤ Y → Y ≠ ⊤ → Y ≤ Subgroup.normalizer (P : Set S)

structure E68Lin3Data (P : Subgroup S) (n : ℕ) : Prop where
  quot_comm : ∀ a ∈ Subgroup.normalizer (P : Set S), ∀ b ∈ Subgroup.normalizer (P : Set S),
    a * b * a⁻¹ * b⁻¹ ∈ P
  order_three : ∀ c ∈ Subgroup.normalizer (P : Set S), orderOf c = 3 →
    4 < (P ⊓ Subgroup.centralizer ({c} : Set S)).relIndex P
  card_root : Nat.card (omegaCenter P) = 2 ^ n
  singer : ∃ x ∈ Subgroup.normalizer (P : Set S), ∀ z ∈ omegaCenter P, z ≠ 1 →
    ∀ w ∈ omegaCenter P, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w
  centralizer_root : ∀ g ∈ omegaCenter P, g ≠ 1 → ∀ y : S, y * g = g * y →
    y ∈ Subgroup.normalizer (P : Set S)
  not_solvable : ∀ Y : Subgroup S, Subgroup.normalizer (P : Set S) < Y → Y ≠ ⊤ →
    ¬ Group.IsSolvable ↥Y

structure E68Sp4Data (P : Subgroup S) (n : ℕ) : Prop where
  quot_comm : ∀ a ∈ Subgroup.normalizer (P : Set S), ∀ b ∈ Subgroup.normalizer (P : Set S),
    a * b * a⁻¹ * b⁻¹ ∈ P
  order_three : ∀ c ∈ Subgroup.normalizer (P : Set S), orderOf c = 3 →
    4 < (P ⊓ Subgroup.centralizer ({c} : Set S)).relIndex P
  card_root : Nat.card (omegaCenter P) = 2 ^ (2 * n)
  split : ∃ Zs Zl : Subgroup S, Zs ≤ omegaCenter P ∧ Zl ≤ omegaCenter P ∧ Zs ⊓ Zl = ⊥ ∧
    Zs ⊔ Zl = omegaCenter P ∧ Nat.card Zs = 2 ^ n ∧ Nat.card Zl = 2 ^ n ∧
    (∀ b ∈ Subgroup.normalizer (P : Set S), ∀ z ∈ Zs, b * z * b⁻¹ ∈ Zs) ∧
    (∀ b ∈ Subgroup.normalizer (P : Set S), ∀ z ∈ Zl, b * z * b⁻¹ ∈ Zl) ∧
    (∃ x ∈ Subgroup.normalizer (P : Set S), (∀ z ∈ Zl, x * z = z * x) ∧
      ∀ z ∈ Zs, z ≠ 1 → ∀ w ∈ Zs, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w) ∧
    (∃ x ∈ Subgroup.normalizer (P : Set S), (∀ z ∈ Zs, x * z = z * x) ∧
      ∀ z ∈ Zl, z ≠ 1 → ∀ w ∈ Zl, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w) ∧
    (∀ y ∈ Subgroup.normalizer (Zs : Set S), ∃ b ∈ Subgroup.normalizer (P : Set S),
      ∀ z ∈ Zs, y * z * y⁻¹ = b * z * b⁻¹) ∧
    (∀ y ∈ Subgroup.normalizer (Zl : Set S), ∃ b ∈ Subgroup.normalizer (P : Set S),
      ∀ z ∈ Zl, y * z * y⁻¹ = b * z * b⁻¹) ∧
    ¬ Subgroup.centralizer (Zs : Set S) ≤ Subgroup.normalizer (P : Set S) ∧
    ¬ Subgroup.centralizer (Zl : Set S) ≤ Subgroup.normalizer (P : Set S)
  centralizer_root : Subgroup.centralizer (omegaCenter P : Set S) ≤
    Subgroup.normalizer (P : Set S)
  not_solvable : ∀ Y : Subgroup S, Subgroup.normalizer (P : Set S) < Y → Y ≠ ⊤ →
    ¬ Group.IsSolvable ↥Y

end Data

structure E68LieFacts : Prop where
  rankOne : ∀ (S : Type) [Group S] [Finite S] (n : ℕ),
    ((2 ≤ n ∧ StatedClassicalModel S .PSL 2 2 n) ∨ (Odd n ∧ 3 ≤ n ∧ SuzukiModel S 2 n) ∨
      (2 ≤ n ∧ StatedClassicalModel S .PSU 3 2 n)) →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → E68RankOneData P n
  lin3 : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 2 ≤ n → StatedClassicalModel S .PSL 3 2 n →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → E68Lin3Data P n
  sp4 : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 2 ≤ n → StatedClassicalModel S .PSp 2 2 n →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → E68Sp4Data P n
  psl25 : ∀ (S : Type) [Group S], StatedClassicalModel S .PSL 2 5 1 →
    StatedClassicalModel S .PSL 2 2 2

end E68Proof

end E6

end CFSG.Quasithin
