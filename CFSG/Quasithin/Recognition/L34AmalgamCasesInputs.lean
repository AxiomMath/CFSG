
module

public import CFSG.Quasithin.Recognition.L34AmalgamGenBase
public meta import CFSG.Quasithin.Recognition.L34AmalgamGenBase
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def cbWords : List String := ["q", "rqR", "", "Rqr"]

@[expose] def cbTabs : List (Array (Fin 22)) := cbWords.map fun s => tab (evalW gen (word s))

@[expose] def repTabs : List (Array (Fin 22)) := (List.finRange 12).map fun i => tab (rep i)

end CFSG.Quasithin.L34Amalgam
