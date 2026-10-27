module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairing
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Two

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.RankThree.PartTwo.Sec4

theorem d4PairingTransTwo_holds :
    D4PairingTransTwo :=
  fun K _ _ q σ hK hσ hq3 c hc hc3 hc1 d hd hd3 hd1 =>
    Item1118Res3ProofU3Two.d4PairingTransTwo_of_mod_two K q σ hK hσ hq3 c hc hc3 hc1 d hd hd3 hd1

end CFSG.RankThree.PartTwo.Sec11

end
