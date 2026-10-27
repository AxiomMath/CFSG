module

public import CFSG.RankThree.Native.LyFaithful
public import CFSG.Sporadic.Ly.Primitive

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native

theorem card_lyP : Nat.card lyP = 51765179004000000 := by
  rw [← Nat.card_congr lyPhiEquiv.toEquiv, card_J]

end CFSG.RankThree.Native
