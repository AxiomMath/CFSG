module

public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def layerCent (I B : Subgroup G) : Subgroup G :=
  inSubgroup CFSG.layer (I ⊓ Subgroup.centralizer (B : Set G))

theorem layerCent_le (I B : Subgroup G) :
    layerCent I B ≤ I ⊓ Subgroup.centralizer (B : Set G) :=
  Subgroup.map_subtype_le _

theorem layerCent_le_left (I B : Subgroup G) : layerCent I B ≤ I :=
  (layerCent_le I B).trans inf_le_left

theorem layerCent_le_centralizer (I B : Subgroup G) :
    layerCent I B ≤ Subgroup.centralizer (B : Set G) :=
  (layerCent_le I B).trans inf_le_right

theorem eq_zpowers_of_card_three {B : Subgroup G} (hB3 : Nat.card B = 3) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) : B = Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB3]; norm_num)
  have hle : Subgroup.zpowers b ≤ B := (Subgroup.zpowers_le).mpr hbB
  have hb' : (⟨b, hbB⟩ : B) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hord : orderOf (⟨b, hbB⟩ : B) = 3 := by
    have h := orderOf_dvd_natCard (⟨b, hbB⟩ : B)
    rw [hB3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hb'
    · exact h3
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, ← Subgroup.orderOf_mk b hbB, hord, hB3]

theorem le_centralizer_of_isElemAbelian {p : ℕ} {A X : Subgroup G} (hAe : IsElemAbelian p A)
    (hXA : X ≤ A) : A ≤ Subgroup.centralizer (X : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hXA hx⟩ ⟨a, ha⟩)

@[expose] def TerminalOrderThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    ((Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
      (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
      (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3)) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ((∀ a ∈ A, ∃ y ∈ layerCent I B,
          y⁻¹ * a ∈ Subgroup.centralizer (layerCent I B : Set G)) ∨
        Nonempty (layerCent I B ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) ∧
      ∃ B₁ B₂ : Subgroup G, B₁ ≤ A ∧ Nat.card B₁ = 3 ∧ B₁ ≤ layerCent I B ⊔ B ∧
        B₂ ≤ A ∧ Nat.card B₂ = 3 ∧ B₂ ≤ layerCent I B₁ ⊔ B₁ ∧ A ≤ layerCent I B₂ ⊔ B₂

@[expose] def Item233Components : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (layerCent (iGroup A) B : Set G)

@[expose] def Item233ComponentsOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (iGroup A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X →
          X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype ∈
            thetaComponentsIn (Subgroup.centralizer (B : Set G))

@[expose] def InnerDiagonalSL34 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Y P : Subgroup H), Y.Normal →
    Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) → IsPGroup 3 P →
      (Y ⊔ Subgroup.centralizer (Y : Set H) ⊔ P).Normal

end CFSG.RankThree.PartTwo.Sec21
