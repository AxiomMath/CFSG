module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Walter.Defs

public section

namespace CFSG.Walter.W67

structure P56AbData (G : Type) [Group G] [Finite G] where
  n : ℕ
  odd_n : Odd n
  three_le_n : 3 ≤ n
  three_dvd_n : 3 ∣ n
  perfect : commutator G = ⊤
  abelian_sylow : HasAbelianSylowTwo G
  elementary_sylow : ∀ S : Sylow 2 G, IsElementaryAbelian 2 (S : Subgroup G)
  no_real_three : ∀ u x t : G, orderOf u = 2 → x ∈ Subgroup.centralizer ({u} : Set G) →
    t ∈ Subgroup.centralizer ({u} : Set G) → x ≠ 1 → x ^ 3 = 1 → t * t = 1 →
    t * x * t⁻¹ ≠ x⁻¹
  centralizer_involution : ∀ u : G, orderOf u = 2 →
    (Nat.card (Subgroup.centralizer ({u} : Set G))).factorization 3 < 2 * n
  J : G
  orderOf_J : orderOf J = 2
  B : Subgroup G
  B_cyclic : IsCyclic B
  card_B : 2 * Nat.card B = 3 ^ n - 1
  B_le : B ≤ Subgroup.centralizer ({J} : Set G)
  E : Subgroup G
  E_cyclic : IsCyclic E
  odd_card_E : Odd (Nat.card E)
  E_le : E ≤ Subgroup.centralizer ({J} : Set G)
  E_le_normalizer_B : E ≤ Subgroup.normalizer (B : Set G)
  E_faithful : ∀ e ∈ E, (∀ b ∈ B, e * b = b * e) → e = 1
  P₀ : Subgroup G
  P₀_le : P₀ ≤ E
  P₀_isPGroup : IsPGroup 3 P₀
  P₀_sylow : (Nat.card P₀).factorization 3 = (Nat.card E).factorization 3
  P₀_ne_bot : P₀ ≠ ⊥
  centralizer_B : ∀ y ∈ P₀, y ≠ 1 → ∀ b ∈ B, y * b = b * y → b ^ (3 ^ (n / 3) - 1) = 1
  P₁ : Subgroup G
  P₂ : Subgroup G
  P₁_elementary : IsElementaryAbelian 3 P₁
  P₂_elementary : IsElementaryAbelian 3 P₂
  card_P₁ : Nat.card P₁ = 3 ^ n
  card_P₂ : Nat.card P₂ = 3 ^ n
  P₁_inf_P₂ : P₁ ⊓ P₂ = ⊥
  P₁_comm_P₂ : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a
  P₁_le : P₁ ≤ Subgroup.centralizer ({J} : Set G)
  J_inv : ∀ y ∈ P₂, J * y * J⁻¹ = y⁻¹
  B_le_normalizer₁ : B ≤ Subgroup.normalizer (P₁ : Set G)
  B_le_normalizer₂ : B ≤ Subgroup.normalizer (P₂ : Set G)
  E_le_normalizer₁ : E ≤ Subgroup.normalizer (P₁ : Set G)
  E_le_normalizer₂ : E ≤ Subgroup.normalizer (P₂ : Set G)
  fixedPointFree₁ : ∀ b ∈ B, b ≠ 1 → ∀ y ∈ P₁, b * y = y * b → y = 1
  fixedPointFree₂ : ∀ b ∈ B, b ≠ 1 → ∀ y ∈ P₂, b * y = y * b → y = 1
  irreducible₁ : ∀ Q : Subgroup G, Q ≤ P₁ → B ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥ ∨ Q = P₁
  irreducible₂ : ∀ Q : Subgroup G, Q ≤ P₂ → B ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥ ∨ Q = P₂
  free : ∀ y ∈ P₀, orderOf y = 3 →
    Nat.card ((P₁ ⊔ P₂) ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ^ 3 =
      Nat.card (P₁ ⊔ P₂ : Subgroup G)
  sylow_centralizer : ∀ Q : Subgroup G, IsPGroup 3 Q →
    Q ≤ Subgroup.centralizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) → Nat.card Q ≤ 3 ^ (2 * n)
  maximal : ∀ Q : Subgroup G, IsPGroup 3 Q → P₁ ⊔ P₂ ≤ Q →
    J ∈ Subgroup.normalizer (Q : Set G) → B ≤ Subgroup.normalizer (Q : Set G) →
    E ≤ Subgroup.normalizer (Q : Set G) → Q = P₁ ⊔ P₂
  normalizer_inf_centralizer_J :
    Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({J} : Set G) ≤
      (Subgroup.zpowers J ⊔ B ⊔ E) ⊔ Subgroup.centralizer ((P₁ ⊔ P₂ : Subgroup G) : Set G)
  centralizer_J_inf : Subgroup.centralizer ({J} : Set G) ⊓
    Subgroup.centralizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) ≤ P₁

end CFSG.Walter.W67
