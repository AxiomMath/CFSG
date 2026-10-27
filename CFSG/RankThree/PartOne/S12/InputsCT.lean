module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL StatedSU)

@[expose] def IsSLModelTwo (n f : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧ Nonempty (X ≃* ↥(StatedSL n K))

@[expose] def IsSUModelTwo (n f : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
    Nonempty (X ≃* ↥(StatedSU n (2 ^ f) K))

@[expose] def CentrallyLThree (f : ℕ) (X : Type) [Group X] : Prop :=
  IsSLModelTwo 3 f X ∨ StatedClassicalModel X .PSL 3 2 f

@[expose] def CentrallyUThree (f : ℕ) (X : Type) [Group X] : Prop :=
  IsSUModelTwo 3 f X ∨ StatedClassicalModel X .PSU 3 2 f

@[expose] def chainAdj {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

variable {G : Type} [Group G]

@[expose] def CTTorusCondition {ι : Type} (p : ℕ) (E : Subgroup G) (K : ι → Subgroup G) : Prop :=
  (∀ i, E = (E ⊓ Subgroup.centralizer (K i : Set G)) ⊔ (E ⊓ K i) ∧
      (E ⊓ Subgroup.centralizer (K i : Set G)).relIndex E = p) ∧
    ∀ i j, i ≠ j →
      (E ⊓ Subgroup.centralizer ((K i ⊔ K j : Subgroup G) : Set G)).relIndex E = p ^ 2

@[expose] def ExtCurtisTitsA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f p : ℕ) (K : Fin n → Subgroup G) (E : Subgroup G),
    3 ≤ n → 2 ≤ f → p.Prime → p ∣ 2 ^ f - 1 → IsElementaryAbelian p E → (⨆ i, K i) = ⊤ →
    (∀ i, StatedClassicalModel (K i) .PSL 2 2 f) →
    (∀ i j, i ≠ j → ¬ chainAdj i j →
      K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥) →
    (∀ i j, chainAdj i j → CentrallyLThree f ↥(K i ⊔ K j)) →
    CTTorusCondition p E K →
    StatedClassicalModel (G ⧸ Subgroup.center G) .PSL (n + 1) 2 f ∧
      (Nat.Coprime (n + 1) (2 ^ f - 1) → StatedClassicalModel G .PSL (n + 1) 2 f)

@[expose] def ExtCurtisTitsCThreeSp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f p : ℕ) (K₁ K₂ K₃ E : Subgroup G),
    2 ≤ f → p.Prime → p ∣ 2 ^ f - 1 → IsElementaryAbelian p E → K₁ ⊔ K₂ ⊔ K₃ = ⊤ →
    StatedClassicalModel K₁ .PSL 2 2 f → StatedClassicalModel K₂ .PSL 2 2 f →
    StatedClassicalModel K₃ .PSL 2 2 f →
    (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) →
    CentrallyLThree f ↥(K₁ ⊔ K₂) → StatedClassicalModel ↥(K₂ ⊔ K₃) .PSp 2 2 f →
    CTTorusCondition p E ![K₁, K₂, K₃] →
    StatedClassicalModel G .PSp 3 2 f

@[expose] def ExtCurtisTitsBThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f p : ℕ) (K₁ K₂ K₃ E : Subgroup G),
    2 ≤ f → p.Prime → p ∣ 2 ^ f - 1 → IsElementaryAbelian p E → K₁ ⊔ K₂ ⊔ K₃ = ⊤ →
    StatedClassicalModel K₁ .PSL 2 2 f → StatedClassicalModel K₂ .PSL 2 2 f →
    StatedClassicalModel K₃ .PSL 2 2 (2 * f) →
    (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) →
    CentrallyLThree f ↥(K₁ ⊔ K₂) → StatedClassicalModel ↥(K₂ ⊔ K₃) .PSU 4 2 f →
    CTTorusCondition p E ![K₁, K₂, K₃] → ¬ (E ⊓ K₂ ≤ Subgroup.centralizer (K₃ : Set G)) →
    StatedClassicalModel G .POmegaMinus 4 2 f

@[expose] def ExtCurtisTitsCThreeU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f p : ℕ) (K₁ K₂ K₃ E : Subgroup G),
    2 ≤ f → p.Prime → p ∣ 2 ^ f - 1 → IsElementaryAbelian p E → K₁ ⊔ K₂ ⊔ K₃ = ⊤ →
    StatedClassicalModel K₁ .PSL 2 2 (2 * f) → StatedClassicalModel K₂ .PSL 2 2 (2 * f) →
    StatedClassicalModel K₃ .PSL 2 2 f →
    (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) →
    CentrallyLThree (2 * f) ↥(K₁ ⊔ K₂) → StatedClassicalModel ↥(K₂ ⊔ K₃) .PSU 4 2 f →
    CTTorusCondition p E ![K₁, K₂, K₃] → ¬ (E ⊓ K₃ ≤ Subgroup.centralizer (K₂ : Set G)) →
    StatedClassicalModel (G ⧸ Subgroup.center G) .PSU 6 2 f

@[expose] def ExtPhan : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f p : ℕ) (K : Fin n → Subgroup G) (E : Subgroup G),
    3 ≤ n → 2 ≤ f → p.Prime → 3 < p → p ∣ 2 ^ f + 1 → IsElementaryAbelian p E →
    (⨆ i, K i) = ⊤ → (∀ i, StatedClassicalModel (K i) .PSL 2 2 f) →
    (∀ i j, i ≠ j → ¬ chainAdj i j →
      K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥) →
    (∀ i j, chainAdj i j → CentrallyUThree f ↥(K i ⊔ K j)) → CTTorusCondition p E K →
    StatedClassicalModel (G ⧸ Subgroup.center G) .PSU (n + 1) 2 f

end CFSG.RankThree.PartOne
