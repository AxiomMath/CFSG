module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def RowModel (p : ℕ) (L : Subgroup G) : ℕ → Prop
  | 1 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f
  | 2 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .G2 0 2 f
  | 3 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .trialityD4 0 2 f
  | 4 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .twistedF4 0 2 f
  | 5 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f
  | 6 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  | 7 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f
  | 8 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f
  | 9 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f
  | 10 => ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f
  | 11 => p = 5 ∧ Nat.card (Subgroup.center L) = 5 ∧ ∃ f : ℕ, 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  | 12 => p = 5 ∧ ¬ 5 ∣ Nat.card (Subgroup.center L) ∧ ∃ f : ℕ, 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
      ¬ 25 ∣ 2 ^ f + 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  | _ => False

@[expose] def RowRank : ℕ → ℕ
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => 2
  | 9 | 10 | 12 => 3
  | 11 => 4
  | _ => 0

@[expose] def RowWeylIso (X : Subgroup G) (Γ : Subgroup (MulAut X)) : ℕ → Prop
  | 1 => Nonempty (Γ ≃* Equiv.Perm (Fin 3))
  | 2 | 3 => Nonempty (Γ ≃* DihedralGroup 6)
  | 4 => Nonempty (Γ ≃* DihedralGroup 8)
  | 5 | 6 | 7 | 8 => Nonempty (Γ ≃* DihedralGroup 4)
  | 9 => Nonempty (Γ ≃* Equiv.Perm (Fin 4))
  | 10 => Nonempty (Γ ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))
  | 11 | 12 => Nonempty (Γ ≃* Equiv.Perm (Fin 5))
  | _ => False

structure Table123Generic [Finite G] (p : ℕ) (L A₀ F : Subgroup G) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  quasisimple : CFSG.IsQuasisimple L
  evenLie : CFSG.Blueprint.EvenLieType (L ⧸ Subgroup.center L)
  evenRank_le : CFSG.Assembly.evenRank ↥L ≤ 3
  center_pPrime : ¬ p ∣ Nat.card (Subgroup.center L)
  localRank_eq : localRank p L = 2
  not_PSL_two : ∀ n : ℕ, ¬ StatedClassicalModel ↥L .PSL n 2 1
  A₀_le : A₀ ≤ L
  A₀_elem : IsElementaryAbelian p A₀
  A₀_card : Nat.card A₀ = p ^ 2
  A₀_invariant : ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
    A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆
  F_le : F ≤ L
  F_elem : IsElementaryAbelian p F
  A₀_le_F : A₀ ≤ F
  F_le_centralizer : F ≤ Subgroup.centralizer (A₀ : Set G)
  F_max : ∀ F' : Subgroup G, F' ≤ L → IsElementaryAbelian p F' →
    F' ≤ Subgroup.centralizer (A₀ : Set G) → F ≤ F' → F' = F

structure Table123SU5 [Finite G] (p : ℕ) (L A₀ F : Subgroup G) : Prop where
  p_eq : p = 5
  quasisimple : CFSG.IsQuasisimple L
  center_card : Nat.card (Subgroup.center L) = 5
  model : ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  A₀_le : A₀ ≤ L
  A₀_elem : IsElementaryAbelian p A₀
  A₀_card : Nat.card A₀ = 5 ^ 3
  center_le : (Subgroup.center L).map L.subtype ≤ A₀
  A₀_invariant : ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
    A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆
  F_le : F ≤ L
  F_elem : IsElementaryAbelian p F
  A₀_le_F : A₀ ≤ F
  F_le_centralizer : F ≤ Subgroup.centralizer (A₀ : Set G)
  F_max : ∀ F' : Subgroup G, F' ≤ L → IsElementaryAbelian p F' →
    F' ≤ Subgroup.centralizer (A₀ : Set G) → F ≤ F' → F' = F

@[expose] def RowData (p : ℕ) (L F : Subgroup G) (r : ℕ) : Prop :=
  RowModel p L r ∧ Nat.card F = p ^ RowRank r ∧ RowWeylIso F (torusImage F L) r ∧
    torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} ∧
    (r ≠ 11 → ∀ B : Subgroup G, B ≤ F → torusInvariant F L B → B = ⊥ ∨ B = F) ∧
    (r = 11 → ∀ B : Subgroup G, B ≤ F → torusInvariant F L B →
      B = ⊥ ∨ B = (Subgroup.center L).map L.subtype ∨ B = F)

@[expose] def KF123 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    (Table123Generic p L A₀ F → ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ r ≠ 11 ∧ RowData p L F r) ∧
    (Table123SU5 p L A₀ F → RowData p L F 11)

@[expose] def KF123NoTransvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    (Table123Generic p L A₀ F ∨ Table123SU5 p L A₀ F) →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → ∀ hy : y ∈ Subgroup.normalizer (F : Set G),
      ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hy⟩)

end CFSG.RankThree.PartOne
