module

public import CFSG.RankThree.GF2n.Tim79a34BigM12
public import CFSG.RankThree.GF2n.Tim79a34BigData
public import CFSG.RankThree.GF2n.Tim79a34BigA9
public import CFSG.RankThree.GF2n.Tim79a34BigWCard
public import CFSG.RankThree.GF2n.Tim79a34BigPLocal
public import CFSG.RankThree.GF2n.Tim79a34BigPCommutator
public import CFSG.RankThree.GF2n.Tim79a34BigPFromLocal
public import CFSG.RankThree.GF2n.Tim79a34BigWCentral
public import CFSG.RankThree.GF2n.Tim79a34BigA9Lemma
public import CFSG.RankThree.GF2n.Tim79a34BigHJLemma
public import CFSG.RankThree.GF2n.Tim79a34BigOddCore
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint

theorem bigPCommutatorStatement_holds (hN : BigNaturalStatement) : BigPCommutatorStatement :=
  bigPCommutatorStatement_of_local hN bigPLocalStatement_holds spRadGeneralStatement_holds

theorem bigPCoverStatement_holds : BigPCoverStatement :=
  bigPCoverStatement_of_local spRadGeneralStatement_holds bigPLocalStatement_holds

theorem bigPDerivedStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) : BigPDerivedStatement :=
  bigPDerivedStatement_of_local hZ hIW (bigPCommutatorStatement_holds hN)

theorem bigPQCommStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigPQCommStatement :=
  bigPQCommStatement_of_local hZ hIW hγ (bigPCommutatorStatement_holds hN)

theorem bigPOrderStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) : BigPOrderStatement :=
  bigPOrderStatement_of_local hZ hN hIW bigPLocalStatement_holds

theorem bigQWStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigQWStatement :=
  bigQWStatement_of_local hZ hN hIW hγ bigPLocalStatement_holds
    (bigPCommutatorStatement_holds hN) bigPCoverStatement_holds

theorem bigWbarCardStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigWbarCardStatement :=
  bigWbarCardStatement_of_qw (bigQWStatement_of_natural hZ hN hIW hγ)

theorem bigRNontrivialStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) : BigRNontrivialStatement :=
  bigRNontrivialStatement_of_local hZ hN hIW bigPLocalStatement_holds

end CFSG.RankThree.GF2n.Tim79a
