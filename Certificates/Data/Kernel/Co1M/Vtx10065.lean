module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CFSG.KD.Co1M

@[expose] def vtxTxt65 : String := include_str "Vtx10065.hex"

@[expose] noncomputable def vtxL65 : Nat → Nat := by hex_tree vtxTxt65 13824 11130335779978059212 384

end CFSG.KD.Co1M

end
