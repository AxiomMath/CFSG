module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Quasithin

open CFSG.CosetTable

@[expose] def u33Letter (c : Char) : Fin 5 × Bool :=
  (⟨"absxy".toList.idxOf c.toLower % 5, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def u33Word (s : String) : List (Fin 5 × Bool) := s.toList.map u33Letter

@[expose] def u33PresRels : List (List (Fin 5 × Bool)) :=
  ["aaaa", "bbbb", "ss", "ABab", "sasB", "sbsA", "xxx", "XaxB", "Xbxba", "xsxs", "yyy",
    "Yabsysaa", "YsaaybA", "Asysay", "sxysXYsxysXYsxysXY"].map u33Word

abbrev u33PresRelsA := restrictWords (subsetOf 5 [0, 1, 2, 3]) u33PresRels

end CFSG.Quasithin
