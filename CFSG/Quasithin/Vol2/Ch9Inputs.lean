module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def Ch9InH11Plus : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)) (n : ℕ),
    (∀ v : V, v ^ 2 = 1) → 1 < n → L ≤ M → M ≤ Subgroup.normalizer (L : Set (MulAut V)) →
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      FFModel.RealizesMod (V := V) (tensorPairModel (CFSG.Assembly.LowTwoRank.StatedSL 2 K)
        (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) L) →
    ∀ A : Subgroup (MulAut V), A ≤ M → A ≠ ⊥ → IsElemAbelian2 A →
      rk A + n ≤ rkIdx (fixV A) + 1 ∧
      (rk A + 2 ≤ rkIdx (fixV A) ∨
        (n = 2 ∧ ∃ t ∈ A, rkIdx (fixV (Subgroup.zpowers t)) = n)) ∧
      (A ≤ L → rk A + n ≤ rkIdx (fixV A))

end CFSG.Quasithin.H13
