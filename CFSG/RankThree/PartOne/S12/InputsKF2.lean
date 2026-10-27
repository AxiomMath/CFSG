module

public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def KF126U4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → 1 ≤ f → p ∣ 2 ^ f + 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f → Nat.card E = p ^ 4 →
    (∀ t ∈ reflectionSet p E, t ∈ torusImage E L →
      (¬ ∃ f' : ℕ, kExceptional p (kZero p E t) f') ∧
      StatedClassicalModel ↥(kZero p E t) .PSL 2 2 f ∧
      E ⊓ Subgroup.centralizer (kZero p E t : Set G) = autFixedInG E t ∧
      autMovedInG E t ≤ kZero p E t ∧
      ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
        k ∈ kZero p E t ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t) ∧
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ t ∈ reflectionSet p E,
      t ∈ torusImage E L → s ≠ t →
      (s * t = t * s → kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
        kZero p E s ⊓ kZero p E t = ⊥) ∧
      (orderOf (s * t) = 3 → CentrallyUThree f ↥(kZero p E s ⊔ kZero p E t)))

end CFSG.RankThree.PartOne
