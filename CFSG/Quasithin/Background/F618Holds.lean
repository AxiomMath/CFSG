module

public import CFSG.Quasithin.Background.F6CatResidualOpen
public import CFSG.Quasithin.Background.F6F613
public import CFSG.Quasithin.Background.GoldschmidtAmalgam
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeV
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPair

public section

namespace CFSG.Quasithin.F6

theorem theoremF618Cat_holds :
    TheoremF618Cat :=
  theoremF618Cat_of_residualRest (f618ResidualRest_of_remaining
    (f618ResidualRemaining_of_goldschmidt (goldschmidtS3ListCat_of_charTwoLarge
      (goldschmidtCharTwoLarge_of_pair GoldAmLarge.goldschmidtCharTwoLargePair_holds.{0}))))

end CFSG.Quasithin.F6
