module

public import CFSG.Walter.W67.JR.RFactsA
public import CFSG.Walter.W67.JR.OutCyclic
public import CFSG.Walter.ReeOrder.JTFinal

public section

namespace CFSG.Walter.W67

theorem rFacts_of :
    S_rFacts_of := rFacts_of_outCyclic outCyclic_of_R

theorem rFacts :
    RFacts := rFacts_of CFSG.Walter.jtThreeHyp

end CFSG.Walter.W67
