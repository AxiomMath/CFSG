module

public import CFSG.RankThree.PartOne.S12.Fusion
public import CFSG.RankThree.PartOne.S12.Sec15

public section

namespace CFSG.RankThree.PartOne

theorem vanishingRecognition_of_nodes' (h11 : Sec11One) (h126 : Node126) (h127 : Node127)
    (h128 : Node128) (hfus : Node12Fusion) (h138 : Node138) (h1320 : Node1320) (h141 : Node141)
    (h1515 : Node1515') (hPU : PushingUpCorollaryΩ) (hlist : KFCGTList) :
    VanishingRecognition :=
  vanishingRecognition_of_sections h11
    (sec12to14_of_nodes h126 h127 h128 (node129_of_fusion hfus) h138 h1320 h141)
    (sec15_of_node1515' h1515 hPU hlist)

end CFSG.RankThree.PartOne
