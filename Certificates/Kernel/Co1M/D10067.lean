module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10067.json.gz" 13146 9429325954181235752
  (RA67 : List Nat) (RTA67 : List Nat) (RS67 : List Nat) (RTS67 : List Nat)
  (LV67 : List (List Nat)) (SZ67 : List Nat)

@[expose] def l0Txt67 : String := include_str "D10067/l0.hex"

@[expose] noncomputable def l0L67 : Nat → Nat := by hex_tree l0Txt67 3200 16236699777378873316 640

@[expose] def l1Txt67 : String := include_str "D10067/l1.hex"

@[expose] noncomputable def l1L67 : Nat → Nat := by hex_tree l1Txt67 1216 4565097158570742161 608

@[expose] def l2Txt67 : String := include_str "D10067/l2.hex"

@[expose] noncomputable def l2L67 : Nat → Nat := by hex_tree l2Txt67 576 2370616151216410000 576

@[expose] def l3Txt67 : String := include_str "D10067/l3.hex"

@[expose] noncomputable def l3L67 : Nat → Nat := by hex_tree l3Txt67 464 9658648769934570979 464

@[expose] def l4Txt67 : String := include_str "D10067/l4.hex"

@[expose] noncomputable def l4L67 : Nat → Nat := by hex_tree l4Txt67 544 4049531367182119402 544

@[expose] def l5Txt67 : String := include_str "D10067/l5.hex"

@[expose] noncomputable def l5L67 : Nat → Nat := by hex_tree l5Txt67 464 17628100747742422610 464

@[expose] def l6Txt67 : String := include_str "D10067/l6.hex"

@[expose] noncomputable def l6L67 : Nat → Nat := by hex_tree l6Txt67 432 4450116019787362016 432

@[expose] def l7Txt67 : String := include_str "D10067/l7.hex"

@[expose] noncomputable def l7L67 : Nat → Nat := by hex_tree l7Txt67 464 10976833778740520995 464

@[expose] def tyTxt67 : String := include_str "D10067/ty.hex"

@[expose] noncomputable def tyL67 : Nat → Nat := by hex_tree tyTxt67 541696 16393141040930290694 736

end CFSG.KD.Co1M

end
