module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Five2cD
public import CFSG.Quasithin.EmptyFaithful.S151ZR
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H23P4

section Five2c

theorem five2cTrivial_of (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) : Five2cTrivial := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L Y hC hX h5 hchar h2C _ hYM _ hY5 _ hVY hYN hYc
  have h3 := input15122L45Block'_holds h118 h126 h37 h38 G T Mc M Z₁ Z₂ V₁ V₂ L hC hchar h2C
  exact (five2c_false hC hX h5 h3 hYM hY5 hVY hYN hYc).elim

end Five2c

end CFSG.Quasithin.H23P4
