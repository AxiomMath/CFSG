module

public import CFSG.Quasithin.EmptyFaithful.S146zNTwoC
public import CFSG.Quasithin.EmptyFaithful.S146zNAmtMain

public section

namespace CFSG.Quasithin

theorem input14624A6Rk_of_amt (hA6 : A6Amt) (hNo : A6NoIrr5) : Input14624A6Rk := by
  intro G _ _ T M S _ K U₁ U₂ s u hctx hKA hKeq X hX
  have hdec : IsDecompUK T M K U₁ U₂ s := hctx.2.2.2.2.2.2.1
  rcases hdec.natural with ⟨hL3, -⟩ | ⟨-, h4 | h5⟩
  · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hKA).elim
  · exact a6rk_rank4 hA6 S hctx hKA hKeq h4 hX
  · exact a6rk_rank5 hA6 hNo S hctx hKA hKeq h5 hX

theorem input14624Two_of_amt (hA6 : A6Amt) (hNo : A6NoIrr5) : Input14624Two :=
  input14624Two_of_a6rk (input14624A6Rk_of_amt hA6 hNo)

theorem input14624Two_of_fin (hF : A6Fin) (hNo : A6NoIrr5) : Input14624Two :=
  input14624Two_of_amt (a6Amt_of_fin hF) hNo

end CFSG.Quasithin
