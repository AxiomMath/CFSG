module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Consequences
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofLate
public import CFSG.RankThree.PartTwo.Sec12.Item128Assembly
public import CFSG.RankThree.PartTwo.Sec21.RonanYS15
public import CFSG.RankThree.PartTwo.Sec6.Item612Proved
public import CFSG.RankThree.PartTwo.Sec6.GF2TypeE27AssemblyCharTwo
public import CFSG.GF2Type.Aschbacher1976Full.Final
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerFalse
public import CFSG.RankThree.PartTwo.Sec4.Item422Holds
public import CFSG.RankThree.PartTwo.Sec18.Item183ETProof
public import CFSG.RankThree.PartTwo.Sec11.Item11CloseNarrow
public import CFSG.RankThree.PartTwo.Sec21.Item64Glue
public import CFSG.GF2Type.Smith1979CharTwoKPInputs
public import CFSG.GF2Type.Smith1979.ParrottThHolds

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo


theorem item2010_of_item1730_item201Contra1
    (h1730 : Sec17.Item1730)
    (h201 : Sec20.Item201Contra1) : Item2010 :=
  item2010_of_item181 Sec4.item4_44_3_holds Sec4.rank3II_4_5
    (Sec18.rank3II_18_1_1_of Sec4.item4_44_1_holds) Sec18.item181_2_holds
    (Sec18.item183ET_of (Sec12.item1210BarS_of
      (Sec12.item128BarAt_of_inputs (Sec11.item1134E27N_of Sec11.Close.narrow_sec9Hyp91SmallNever))
      item4_22_holds Sec4.rank3II_4_5) h1730) h201

end CFSG.RankThree.PartTwo.Late

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo


theorem item236_of_item231_item233
    (h231 : Item231) (h233 : Item233) : Item236 :=
  item236_of_items
    (item64One_of_item6_4_1 (Sec6.rank3II_6_4_1_of_e27 (Sec6.gf2TypeE27_of_inputs''
      CFSG.GF2Type.Aschbacher1976Full.aschbacher1976Statement_holds
      (CFSG.GF2Type.smith1979CharTwoKP_of_widthFour CFSG.GF2Type.Smith1979.parrottThKP_holds
        CFSG.GF2Type.Smith1979.OmegaPlus.widthFourOmegaPlusLayerFalse_holds))))
    (item612Sec21_of_items Sec6.rank3II_6_12_sec21_closed (Sec6.item45_of_item4_5 Sec4.rank3II_4_5))
    h233 (rank3II_23_4_of_gl83Simple h231 h233 RonanYS15.gl83StronglyEmbeddedNoSimpleThree_holds)
    (CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1)

end CFSG.RankThree.PartTwo.Sec21
