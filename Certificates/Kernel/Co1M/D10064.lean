module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1M

#kc_repo #kc_json_gz CFSG.KD.Co1M
  "Certificates/Kernel/Co1M/data/D10064.json.gz" 162743 11785422224961214869
  (R64 : List Nat) (RT64 : List Nat) (P64 : List (List (Nat × Nat))) (RS64 : List Nat)
  (RST64 : List Nat) (PS64 : List (List (Nat × Nat))) (Q64 : Nat) (QI64 : Nat) (BASE64 : List Nat)
  (LV64 : List (List Nat)) (SZ64 : List Nat) (E64 : List Nat) (CN64 : List Nat)
  (CM64 : List (List Nat)) (L64 : List Nat) (CL64 : List Nat) (CLG64 : List Nat) (PVL64 : List Nat)
  (PP64 : List Nat) (CP64 : List Nat) (PVP64 : List Nat) (U64 : List Nat)

@[expose] def l0Txt64 : String := include_str "D10064/l0.hex"

@[expose] noncomputable def l0L64 : Nat → Nat := by hex_tree l0Txt64 43008 14848217319441453164 672

@[expose] def l1Txt64 : String := include_str "D10064/l1.hex"

@[expose] noncomputable def l1L64 : Nat → Nat := by hex_tree l1Txt64 560 1789896054368552848 560

end CFSG.KD.Co1M

end
