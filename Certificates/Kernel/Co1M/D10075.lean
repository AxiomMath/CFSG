module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10075.json.gz" 1194 6290638718062387932
  (RS1v75 : Nat) (RS2v75 : Nat) (RGv75 : Nat) (RT75 : List Nat) (RGt75 : Nat) (gWord75 : List Bool)
  (u3v75 : Nat) (w3v75 : Nat)

@[expose] def t3Txt75 : String := include_str "D10075/t3.hex"

@[expose] noncomputable def t3L75 : Nat → Nat := by hex_tree t3Txt75 541696 14654325966514895841 736

@[expose] def t4Txt75 : String := include_str "D10075/t4.hex"

@[expose] noncomputable def t4L75 : Nat → Nat := by hex_tree t4Txt75 535808 12863052919216950158 736

@[expose] def j3Txt75 : String := include_str "D10075/j3.hex"

@[expose] noncomputable def j3L75 : Nat → Nat := by hex_tree j3Txt75 4608 7956136886944494532 512

@[expose] def j4Txt75 : String := include_str "D10075/j4.hex"

@[expose] noncomputable def j4L75 : Nat → Nat := by hex_tree j4Txt75 4608 3205599464787678498 512

end CFSG.KD.Co1M

end
