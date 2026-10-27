module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Sporadic.Bridge.Common
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Open

@[expose] def u33CLetter (c : Char) : Fin 3 × Bool :=
  (⟨"abs".toList.idxOf c.toLower % 3, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def u33CRels : List (List (Fin 3 × Bool)) :=
  ["aaaa", "bbbb", "ss", "ABab", "sasB", "sbsA"].map fun s => s.toList.map u33CLetter

end CFSG.Quasithin
