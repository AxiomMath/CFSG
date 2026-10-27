module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def IsSymplecticTransvectionIn (k : ℕ) {F : Type} [Field F] (g : ↥(StatedSp k F)) :
    Prop :=
  Matrix.rank (((g : GL (Fin k ⊕ Fin k) F) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) - 1) = 1

@[expose] def IsSymplecticTransvection (X : Type) [Group X] (m n : ℕ) (x : X) : Prop :=
  ∃ k : ℕ, m = 2 * k ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ e : (X ⧸ Subgroup.center X) ≃* ↥(StatedSp k F),
      IsSymplecticTransvectionIn k (e (QuotientGroup.mk x))

end CFSG.LocalAnalysis.WeakClosure81.SevenK
