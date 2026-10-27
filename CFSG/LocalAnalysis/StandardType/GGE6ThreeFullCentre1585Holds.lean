module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Cyclic
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowCokerAHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowCokerBHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableAHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableBHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableCHolds

public section

namespace CFSG.StandardType.E6Centralizer1585

theorem e6FullCentreCyclicR1_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    GGE6ThreeFullCentreCyclicOn1585 Omega GGE6ThreeR1Labels1585 :=
  fullCentreCyclicOn_of_rowCoker Omega _
    (e6RowCokerCyclicR1_of_pieces Omega e6RowTableR1_holds nodeCokerCyclicR1_holds)

theorem e6FullCentreCyclicR3_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    GGE6ThreeFullCentreCyclicOn1585 Omega GGE6ThreeR3Labels1585 :=
  fullCentreCyclicOn_of_rowCoker Omega _
    (e6RowCokerCyclicR3_of_pieces Omega e6RowTableR3_holds nodeCokerCyclicR3_holds)

theorem e6FullCentreCyclicR4_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    GGE6ThreeFullCentreCyclicOn1585 Omega GGE6ThreeR4Labels1585 :=
  fullCentreCyclicOn_of_rowCoker Omega _
    (e6RowCokerCyclicR4_of_pieces Omega e6RowTableR4_holds nodeCokerCyclicR4_holds)

theorem e6FullCentreCyclicR16_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    GGE6ThreeFullCentreCyclicOn1585 Omega GGE6ThreeR16Labels1585 :=
  fullCentreCyclicOn_of_rowCoker Omega _
    (e6RowCokerCyclicR16_of_pieces Omega e6RowTableR16_holds nodeCokerCyclicR16_holds)

theorem e6FullCentreCyclicR4Opp_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    GGE6ThreeFullCentreCyclicOn1585 Omega GGE6ThreeR4OppLabels1585 :=
  fullCentreCyclicOn_of_rowCoker Omega _
    (e6RowCokerCyclicR4Opp_of_pieces Omega e6RowTableR4Opp_holds nodeCokerCyclicR4Opp_holds)

theorem e6FullCentreCyclicR16Opp_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    GGE6ThreeFullCentreCyclicOn1585 Omega GGE6ThreeR16OppLabels1585 :=
  fullCentreCyclicOn_of_rowCoker Omega _
    (e6RowCokerCyclicR16Opp_of_pieces Omega e6RowTableR16Opp_holds nodeCokerCyclicR16Opp_holds)

end CFSG.StandardType.E6Centralizer1585

end
