module

public import CFSG.RankThree.PartTwo.Sec11.DataExistsProof

public section

namespace CFSG.RankThree.PartTwo.Sec11

theorem item1134_of_steps_data (h812 : Sec8.Item812) (h1016 : Sec10.Item1016)
    (h97 : Sec9.Item97) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h1116 : Item1116) (h1117 : Item1117)
    (hset : SetUp1118) (h1119 : Item1119) (h1123 : Item1123) (hinv : Inverter1118)
    (hch : Choose1128) (h1132 : Item1132) : Item1134 :=
  item1134_of_steps h812 h1016 h97 h45 h48 h113 h117 (sec11DataExists_of h97 h45 h113 h117 h119)
    h1116 h1117 hset h1119 h1123 hinv hch h1132

end CFSG.RankThree.PartTwo.Sec11
