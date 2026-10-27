module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.LargeExtraspecial.S8CBFSmall
public import CFSG.Quasithin.Background.GoldschmidtShultBender

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem borelRankOneSolvable_holds :
    BorelRankOneSolvableStatement := by
  intro X _ _ hX T hT hT2
  have hB : CFSG.Open.fusionIsBenderGroup X := by
    rcases hX with ⟨s, hs, h⟩ | ⟨s, hs, h⟩ | ⟨s, -, -, h⟩
    · exact CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psl_two hs h
    · exact CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psu_three hs h
    · exact CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_twistedB2 h
  exact CFSG.Quasithin.Shult.isSolvable_normalizer_of_bender hB hT hT2

end CFSG.RankThree.GF2n.Stroth80
