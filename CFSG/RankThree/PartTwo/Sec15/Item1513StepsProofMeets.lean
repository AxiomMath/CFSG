module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1513Steps

theorem step1513Meets_of
    (h131 : Item131) (h133 : Item133) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511StarR) (hpt : Step1513MeetsPoint) : Step1513Meets := by
  intro G _ _ A c L a K hctx Y hY
  have h := hctx.toSec15R
  obtain ⟨c', L', hc', hL', hm⟩ := hpt G A c L h (fun b Lb hb hLb =>
    not_j2_of_irreducible h131 h134 h48 h415 h hctx.irreducible hctx.card_inf hb hLb) Y hY.prop
  exact meetsY4_of_point h131 h133 h134 h48 h415 h137 hcl h hctx.irreducible hctx.card_inf
    hctx.normalizer_le hY.prop
    (fun c'' L'' h'' p e _ he hiso hm' P hAP hP =>
      (h1511 G A c'' L'' h'' p e he hiso Y hY hm' P hAP hP).1) hc' hL' hm

end CFSG.RankThree.PartTwo.Sec15
