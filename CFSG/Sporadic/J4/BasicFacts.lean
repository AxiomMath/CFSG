module

public import CFSG.Sporadic.J4.Local

public section

namespace CFSG.Sporadic.J4

open QT2

structure J4Basic : Prop where
  mat : MatFacts
  cardHj : Nat.card Hj = 501397585920
  cardJ : Nat.card J = 86775571046077562880
  stab : ∀ x : J, x • toRow Native.rootV.toVec = toRow Native.rootV.toVec → x ∈ Hj

end CFSG.Sporadic.J4

end
