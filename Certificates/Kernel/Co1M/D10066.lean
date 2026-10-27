module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10066.json.gz" 2462 3218610519062346644
  (R0v66 : Nat) (R1v66 : Nat) (W3a66 : List Nat) (W3b66 : List Nat) (W4a66 : List Nat)
  (W4b66 : List Nat) (G366 : List Nat) (GT366 : List Nat) (G466 : List Nat) (GT466 : List Nat)
  (Rt366 : List Nat) (Sz366 : List Nat) (Rt466 : List Nat) (Sz466 : List Nat)

@[expose] def t30Txt66 : String := include_str "D10066/t30.hex"

@[expose] noncomputable def t30L66 : Nat → Nat := by hex_tree t30Txt66 5760 18055830909291605645 640

@[expose] def t31Txt66 : String := include_str "D10066/t31.hex"

@[expose] noncomputable def t31L66 : Nat → Nat := by hex_tree t31Txt66 445936 2760367991762164514 752

@[expose] def t32Txt66 : String := include_str "D10066/t32.hex"

@[expose] noncomputable def t32L66 : Nat → Nat := by hex_tree t32Txt66 571520 1627456347474189585 752

@[expose] def t33Txt66 : String := include_str "D10066/t33.hex"

@[expose] noncomputable def t33L66 : Nat → Nat := by hex_tree t33Txt66 126000 11100051589544314716 720

@[expose] def p3Txt66 : String := include_str "D10066/p3.hex"

@[expose] noncomputable def p3L66 : Nat → Nat := by hex_tree p3Txt66 491520 4638141676633440678 320

@[expose] def t40Txt66 : String := include_str "D10066/t40.hex"

@[expose] noncomputable def t40L66 : Nat → Nat := by hex_tree t40Txt66 558624 12936895661500440672 736

@[expose] def t41Txt66 : String := include_str "D10066/t41.hex"

@[expose] noncomputable def t41L66 : Nat → Nat := by hex_tree t41Txt66 565248 14633427189133865437 736

@[expose] def t42Txt66 : String := include_str "D10066/t42.hex"

@[expose] noncomputable def t42L66 : Nat → Nat := by hex_tree t42Txt66 5760 6452726225950391705 640

@[expose] def p4Txt66 : String := include_str "D10066/p4.hex"

@[expose] noncomputable def p4L66 : Nat → Nat := by hex_tree p4Txt66 491520 17421462237714818168 320

end CFSG.KD.Co1M

end
