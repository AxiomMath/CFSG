module

public import CFSG.Sporadic.ThSchreier.GlobalData
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Pointwise

@[expose] def chainSmallRows : List ℕ := hexsOf (include_str "Data/ChainSmallRows.txt")

@[expose] def chainPerm0 : List ℕ := natsOf (include_str "Data/ChainPerm0.txt")

@[expose] def chainPerm1 : List ℕ := natsOf (include_str "Data/ChainPerm1.txt")

end CFSG.Sporadic.ThSchreier
