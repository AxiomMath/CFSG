module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoRef
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.Quasithin.L34Amalgam

open CFSG.CosetTable

@[expose] def a5Rels : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true)]]

end CFSG.Quasithin.L34Amalgam
