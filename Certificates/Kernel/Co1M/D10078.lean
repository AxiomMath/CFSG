module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10078.json.gz" 27134 13015549671765650476
  (R78 : List Nat) (RT78 : List Nat) (X78 : List Nat) (F1178 : List Nat) (Y1178 : List Nat)
  (W1178 : List Nat) (F778 : List Nat) (Y778 : List Nat) (W778 : List Nat) (F578 : List Nat)
  (Y578 : List Nat) (W578 : List Nat)

@[expose] def t11aTxt78 : String := include_str "D10078/t11a.hex"

@[expose] noncomputable def t11aL78 : Nat → Nat := by hex_tree t11aTxt78 238464 13302115231465682254 736

@[expose] def t11bTxt78 : String := include_str "D10078/t11b.hex"

@[expose] noncomputable def t11bL78 : Nat → Nat := by hex_tree t11bTxt78 7040 7962490249981482235 640

@[expose] def t7aTxt78 : String := include_str "D10078/t7a.hex"

@[expose] noncomputable def t7aL78 : Nat → Nat := by hex_tree t7aTxt78 238464 16953601417535768958 736

@[expose] def t7bTxt78 : String := include_str "D10078/t7b.hex"

@[expose] noncomputable def t7bL78 : Nat → Nat := by hex_tree t7bTxt78 28224 11106033088368105249 672

@[expose] def t7cTxt78 : String := include_str "D10078/t7c.hex"

@[expose] noncomputable def t7cL78 : Nat → Nat := by hex_tree t7cTxt78 512 2894458423458238661 512

@[expose] def t5aTxt78 : String := include_str "D10078/t5a.hex"

@[expose] noncomputable def t5aL78 : Nat → Nat := by hex_tree t5aTxt78 287040 10190915267042105134 736

@[expose] def t5bTxt78 : String := include_str "D10078/t5b.hex"

@[expose] noncomputable def t5bL78 : Nat → Nat := by hex_tree t5bTxt78 66048 17629301855949143664 688

@[expose] def t5cTxt78 : String := include_str "D10078/t5c.hex"

@[expose] noncomputable def t5cL78 : Nat → Nat := by hex_tree t5cTxt78 512 8251012973735301228 512

@[expose] def cl11Txt78 : String := include_str "D10078/cl11.hex"

@[expose] noncomputable def cl11L78 : Nat → Nat := by hex_tree cl11Txt78 9392 1178559939169273892 4696

@[expose] def n5Txt78 : String := include_str "D10078/n5.hex"

@[expose] noncomputable def n5L78 : Nat → Nat := by hex_tree n5Txt78 18816 15902888036886615409 4704

@[expose] def s0Txt78 : String := include_str "D10078/s0.hex"

@[expose] noncomputable def s0L78 : Nat → Nat := by hex_tree s0Txt78 108928 4040116863604541015 4736

@[expose] def e0Txt78 : String := include_str "D10078/e0.hex"

@[expose] noncomputable def e0L78 : Nat → Nat := by hex_tree e0Txt78 5760 15933823280742517212 480

@[expose] def c0Txt78 : String := include_str "D10078/c0.hex"

@[expose] noncomputable def c0L78 : Nat → Nat := by hex_tree c0Txt78 11040 14064673319351611328 480

end CFSG.KD.Co1M

end
