module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Big
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Two
public import CFSG.Quasithin.EmptyFaithful.S151Ch3Bridge
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Quasithin

theorem lemma319SixGoodBig_of_inputs (hC58 : TheoremC58) (h317 : AS317Sylow) : Lemma319SixGoodBig :=
  lemma319SixGoodBig_of (theorem317Statement_of_inputs hC58 h317)

theorem lemma319SixGood_of_residual (hC58 : TheoremC58) (h317 : AS317Sylow) (hB69 : B69Struct)
    (hB1 : B69One) (hres : Six6TwoIndex) : Lemma319SixGood :=
  lemma319SixGood_of hB69 hB1 (lemma319SixGoodBig_of_inputs hC58 h317)
    (lemma319SixGoodTwo_of hB69 (theorem317Statement_of_inputs hC58 h317) hres)

end CFSG.Quasithin.H13.L319

