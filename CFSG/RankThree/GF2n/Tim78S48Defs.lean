module

public import CFSG.RankThree.GF2n.Tim78Lemma218

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

structure Hyp48 (M B T : Subgroup G) (g : G) : Prop where
  leM : conjSubgroup g B ≤ M
  comm_T : ∀ a ∈ conjSubgroup g B, ∀ t ∈ T, ⁅a, t⁆ ∈ B
  comm_Tg : ∀ b ∈ B, ∀ t ∈ conjSubgroup g T, ⁅b, t⁆ ∈ conjSubgroup g B

abbrev kernel48 (B T : Subgroup G) (g : G) : Subgroup G :=
  (T ⊔ conjSubgroup g T) ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)

@[expose] def Phase1a (Q B T : Subgroup G) (g : G) : Prop :=
  Assembly.IsElemAbelian 2 (kernel48 B T g) ∧
  kernel48 B T g = (T ⊓ kernel48 B T g) ⊔ (conjSubgroup g T ⊓ kernel48 B T g) ∧
  T ⊓ conjSubgroup g T = T ⊓ conjSubgroup g Q ∧
  T ⊓ kernel48 B T g = T ⊓ Subgroup.centralizer ((conjSubgroup g B : Subgroup G) : Set G) ∧
  ((∃ f : ℕ, 2 ≤ f ∧ (T ⊓ kernel48 B T g).relIndex T = 2 ^ f ∧
      ∃ _ : ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal,
        Nonempty (↥(T ⊔ conjSubgroup g T) ⧸ (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T) ≃*
          PSL(2, GaloisField 2 f))) ∨
    (∃ a : ℕ, 1 ≤ a ∧ (T ⊓ kernel48 B T g).relIndex T = 2 ^ (2 * a + 1) ∧
      ∃ _ : ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal,
        Nonempty (↥(T ⊔ conjSubgroup g T) ⧸ (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T) ≃*
          Sz a)) ∨
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ (T ⊓ kernel48 B T g).relIndex T = 2 ∧
      ∃ _ : ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal,
        Nonempty (↥(T ⊔ conjSubgroup g T) ⧸ (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T) ≃*
          DihedralGroup m)))

@[expose] def Phase1 (B T : Subgroup G) (g : G) : Prop :=
  ∃ n : ℕ, Nat.card B = 2 ^ n ∧
    InducesNaturalSL2 n (T ⊔ conjSubgroup g T) (B ⊔ conjSubgroup g B) ∧
    (∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 → ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U) ∧
    (∀ U ∈ classIn B (B ⊔ conjSubgroup g B), ∃ h ∈ T ⊔ conjSubgroup g T, U = conjSubgroup h B) ∧
    Assembly.IsElemAbelian 2 ((T ⊔ conjSubgroup g T) ⊓
      Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)) ∧
    (T ⊔ conjSubgroup g T) ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) =
      (B ⊔ conjSubgroup g B) ⊔ (T ⊓ conjSubgroup g T) ∧
    (B ⊔ conjSubgroup g B) ⊓ (T ⊓ conjSubgroup g T) = ⊥ ∧ T ⊓ conjSubgroup g T ≠ ⊥ ∧
    (∀ h ∈ T ⊔ conjSubgroup g T, ∀ k ∈ (T ⊔ conjSubgroup g T) ⊓
      Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
      ⁅h, k⁆ ∈ B ⊔ conjSubgroup g B) ∧
    (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B ∧
    ∃ K₁ : Subgroup G, K₁ ≤ T ⊔ conjSubgroup g T ∧ K₁ ≤ Subgroup.normalizer (B : Set G) ∧
      K₁ ≤ Subgroup.normalizer ((conjSubgroup g B : Subgroup G) : Set G) ∧ IsCyclic K₁ ∧
      Nat.card K₁ = Nat.card B - 1 ∧
      K₁ ≤ Subgroup.centralizer ((T ⊓ conjSubgroup g T : Subgroup G) : Set G) ∧
      (∀ x ∈ K₁, x ≠ 1 → ∀ b ∈ B, x * b * x⁻¹ = b → b = 1) ∧
      (∀ U ∈ classIn B (B ⊔ conjSubgroup g B), (∀ k ∈ K₁, conjSubgroup k U = U) →
        U = B ∨ U = conjSubgroup g B)

structure EndgameData (M B Q P T : Subgroup G) (g : G) (C L : Subgroup G) : Prop where
  hC : ∀ c : G, c ∈ C ↔ c ∈ P ∧ ∀ y ∈ conjSubgroup g B, ⁅c, y⁆ ∈ B
  hL : L = C ⊔ conjSubgroup g B
  B_le_C : B ≤ C
  C_elem : Assembly.IsElemAbelian 2 C
  C_cent : ∀ c ∈ C, ∀ y ∈ conjSubgroup g B, c * y = y * c
  C_inf : C ⊓ conjSubgroup g B = ⊥
  card_C : Nat.card C = Nat.card B * C.relIndex P
  L_elem : Assembly.IsElemAbelian 2 L
  relIndex_L : C.relIndex L = Nat.card B
  Q_norm : Q ≤ Subgroup.normalizer (L : Set G)
  Q_comm : ∀ x ∈ Q, ∀ l ∈ L, ⁅x, l⁆ ∈ C
  T_comm : ∀ t ∈ T, ∀ l ∈ L, ⁅l, t⁆ ∈ B
  T_rel : (T ⊓ Subgroup.centralizer (L : Set G)).relIndex T = Nat.card B
  part : ∀ l ∈ L, l ≠ 1 → ∃! U, U ∈ classIn B L ∧ l ∈ U
  trans : ∀ U ∈ classIn B L, ∃ r ∈ Subgroup.normalizer (L : Set G), U = conjSubgroup r B
  Bg_inf : conjSubgroup g B ⊓ Q = ⊥

@[expose] def Step48 (M B P T : Subgroup G) : Prop :=
  ∀ g : G, Hyp48 M B T g → conjSubgroup g B ≤ P

end CFSG.RankThree.GF2n.Tim78
