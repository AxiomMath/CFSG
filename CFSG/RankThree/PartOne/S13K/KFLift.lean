module

public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def KFLiftAt {G : Type} [Group G] (p : ℕ) (E : Subgroup G) (t : MulAut E) : Prop :=
  CFSG.IsQuasisimple ↥(kZero p E t) ∧ Subgroup.center ↥(kZero p E t) = ⊥ ∧
    (¬ ∃ f : ℕ, kExceptional p (kZero p E t) f) ∧ autMovedInG E t ≤ kZero p E t ∧
    ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ kZero p E t ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = t

theorem KFLiftAt.isKt {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {t : MulAut E}
    (h : KFLiftAt p E t) : IsKt p E t (kZero p E t) :=
  ⟨fun f hf => absurd ⟨f, hf⟩ h.2.2.1, fun _ => rfl⟩

@[expose] def KFLiftRowOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → E = A → RowModel p L 1 →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFLiftAt p E t

@[expose] def KFLiftRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → E ≠ A → RowModel p L r →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFLiftAt p E t

@[expose] def KFLiftAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    (E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J)) →
    ∀ t ∈ reflectionSet p E, KFLiftAt p E t

@[expose] def RowModelF (p : ℕ) {G : Type} [Group G] (L : Subgroup G) (r f : ℕ) : Prop :=
  match r with
  | 1 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f
  | 2 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .G2 0 2 f
  | 3 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .trialityD4 0 2 f
  | 4 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .twistedF4 0 2 f
  | 5 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f
  | 6 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  | 7 => 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f
  | 8 => 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f
  | 9 => 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f
  | 10 => 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f
  | 11 => p = 5 ∧ Nat.card (Subgroup.center L) = 5 ∧ 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  | 12 => p = 5 ∧ ¬ 5 ∣ Nat.card (Subgroup.center L) ∧ 1 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧ ¬ 25 ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  | _ => False

@[expose] def KRowType {G : Type} [Group G] (r f : ℕ) (K : Subgroup G) : Prop :=
  match r with
  | 1 | 2 | 7 | 9 | 10 | 11 | 12 => StatedClassicalModel ↥K .PSL 2 2 f
  | 3 => StatedClassicalModel ↥K .PSL 2 2 f ∨ StatedClassicalModel ↥K .PSL 2 2 (3 * f)
  | 4 => StatedClassicalModel ↥K .PSL 2 2 f ∨ CFSG.Blueprint.LieModel ↥K .twistedB2 0 2 f
  | 5 | 6 | 8 => StatedClassicalModel ↥K .PSL 2 2 f ∨ StatedClassicalModel ↥K .PSL 2 2 (2 * f)
  | _ => False

@[expose] def KF132Types (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → RowModel p L r → (r ≤ 8 → E = A) →
    (9 ≤ r → Nat.card E = p ^ 4) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
      ∃ f : ℕ, RowModelF p L r f ∧ KRowType r f K ∧ (r ≤ 8 → autMovedInG E t ≤ K)

end CFSG.RankThree.PartOne.S13K
