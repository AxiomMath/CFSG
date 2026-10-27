module

public import CFSG.RankThree.PartOne.KF.BloomPrime
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3

public section

namespace CFSG.RankThree.PartOne

theorem extBloomMitchell_holds : ExtBloomMitchell := fun _ _ hp2 {_} hG =>
  CFSG.RankThree.SubgroupLists.bloom_mitchell_irreducible_gl_three hp2 hG

theorem extBloomPrime_holds : ExtBloomPrime := extBloomPrime_of_mitchell extBloomMitchell_holds

end CFSG.RankThree.PartOne
