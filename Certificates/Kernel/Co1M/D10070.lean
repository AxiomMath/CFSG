module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10070.json.gz" 29251 17826244020424592152
  (R70 : List Nat) (RT70 : List Nat) (P70 : List (List (Nat × Nat))) (a0v70 : Nat) (a1v70 : Nat)
  (w0v70 : Nat) (w1v70 : Nat) (K1x70 : List Nat) (K2x70 : List Nat) (K2ix70 : List Nat)
  (K3x70 : List Nat) (K3ix70 : List Nat) (K4x70 : List Nat) (K4ix70 : List Nat) (Rt1x70 : List Nat)
  (Rt2x70 : List Nat) (Rt3x70 : List Nat) (uBv70 : Nat) (wBv70 : Nat) (KBx70 : List Nat)
  (uCv70 : Nat) (wCv70 : Nat) (KCx70 : List Nat) (SAt70 : Nat) (QP70 : Nat) (Qt70 : Nat)
  (FA70 : List Nat) (YA70 : List Nat) (FAt70 : List Nat) (FB70 : List Nat) (YB70 : List Nat)
  (FC70 : List Nat) (YC70 : List Nat) (QS70 : List Nat) (OFF70 : List Nat)

@[expose] def t1Txt70 : String := include_str "D10070/t1.hex"

@[expose] noncomputable def t1L70 : Nat → Nat := by hex_tree t1Txt70 423640 9621278217401122503 4760

@[expose] def t2Txt70 : String := include_str "D10070/t2.hex"

@[expose] noncomputable def t2L70 : Nat → Nat := by hex_tree t2Txt70 18816 5324801816845373996 4704

@[expose] def t3Txt70 : String := include_str "D10070/t3.hex"

@[expose] noncomputable def t3L70 : Nat → Nat := by hex_tree t3Txt70 80376 7124862533701285571 4728

@[expose] def v1Txt70 : String := include_str "D10070/v1.hex"

@[expose] noncomputable def v1L70 : Nat → Nat := by hex_tree v1Txt70 1824 8411763061923317574 608

@[expose] def v0Txt70 : String := include_str "D10070/v0.hex"

@[expose] noncomputable def v0L70 : Nat → Nat := by hex_tree v0Txt70 3040 4623111946252245581 608

@[expose] def vbTxt70 : String := include_str "D10070/vb.hex"

@[expose] noncomputable def vbL70 : Nat → Nat := by hex_tree vbTxt70 20992 9782774079375808559 656

@[expose] def vcTxt70 : String := include_str "D10070/vc.hex"

@[expose] noncomputable def vcL70 : Nat → Nat := by hex_tree vcTxt70 20992 4619104574615135363 656

end CFSG.KD.Co1M

end
