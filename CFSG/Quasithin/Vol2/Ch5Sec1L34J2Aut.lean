module

public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.Sporadic.J2

public section

namespace CFSG.Quasithin.H13

@[expose] def mulAutCongrOfMulEquiv {G H : Type*} {iG : Mul G} {iH : Mul H} (e : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun f := (e.symm.trans f).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp [MulAut.mul_apply]

theorem card_mulAut_eq_of_mulEquiv {G H : Type*} {iG : Mul G} {iH : Mul H} (e : G ≃* H) :
    Nat.card (MulAut G) = Nat.card (MulAut H) :=
  Nat.card_congr (mulAutCongrOfMulEquiv e).toEquiv

theorem card_mulAut_quasithinJ2 :
    Nat.card (MulAut CFSG.Open.quasithinJ2) = 1209600 := by
  rw [card_mulAut_eq_of_mulEquiv CFSG.Quasithin.quasithinJ2MulEquivNative,
    CFSG.ComponentClassification.J2Cover.j2_mulAut_card, CFSG.Sporadic.J2.card_J2]

end CFSG.Quasithin.H13
