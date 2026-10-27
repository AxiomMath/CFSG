
module


public import CFSG.Sporadic.J4.Simple
public import Certificates.Certificate3084

public section

namespace CFSG.Sporadic.J4

open CFSG.Blueprint

theorem j4Facts : J4Facts := Certificates.certificate3084

theorem isSimpleGroup_J4 : IsSimpleGroup NativeSporadic.J4 :=
  @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_J j4Facts) (seedEquiv j4Facts.mat)

theorem fam_j4_simplicity :
    Finite NativeSporadic.J4 ∧ Nontrivial NativeSporadic.J4 ∧
    IsSimpleGroup NativeSporadic.J4 :=
  ⟨Finite.of_equiv _ (seedEquiv j4Facts.mat).toEquiv.symm, isSimpleGroup_J4.toNontrivial,
    isSimpleGroup_J4⟩

theorem card_J4 :
    Nat.card NativeSporadic.J4 = 86775571046077562880 := by
  rw [Nat.card_congr (seedEquiv j4Facts.mat).toEquiv, card_J j4Facts]

end CFSG.Sporadic.J4
