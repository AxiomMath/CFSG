
module

public import CFSG.Sporadic.ThSchreier.RowBase
public import CFSG.Sporadic.Th.ChainBase
public import CFSG.Sporadic.Th.Max3.PacketBase
public import CFSG.Sporadic.Th.Max3.AllConjBase
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.Th.IndexBase
public import CFSG.Sporadic.Th.Max3.AllConjInputsBase
public import CFSG.Sporadic.Th.Max3.InvolutionsBase
public import CFSG.Sporadic.Th.Max3.InvolutionsInputsBase
public import CFSG.Sporadic.Th.Max3.QuotientBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def localRowsTxt : String := include_str "Data/LocalRows.txt"

@[expose] def localRowNats : List ℕ := hexsOf localRowsTxt

end CFSG.Sporadic.ThSchreier
