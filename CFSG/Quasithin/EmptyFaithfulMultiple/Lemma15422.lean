module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Cat
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate4952

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt15422_of
    (hF618 : F6.TheoremF618Cat) {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) (hnot : ¬ IsLThreeTwoOrASix G)
    (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) (h17 : Stmt15417 G T) (h19 : Stmt15419 G T)
    (h20 : Stmt15420 G T) : Stmt15422 G T :=
  stmt15422_of_cat hF618 (fun s => isSQTKCat_of_hyp hyp (h19 s).2.2.1) hyp hnot h12 h14 h17 h19
    h20

end CFSG.Quasithin.EmptyFaithfulMultiple
