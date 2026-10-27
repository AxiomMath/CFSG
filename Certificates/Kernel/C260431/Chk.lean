module

public import Certificates.Data.Kernel.B45Nor.Defs
public import Certificates.Data.SmithB45MatIndM23Nor
public import Certificates.Kernel.C260431.Data

public section

namespace CFSG.KD.C260431

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

@[expose] noncomputable def ht23 (t : ℕ) (z : Bool) : List ℕ :=
  match t with
  | 1 => (List.range 11).map (rowK (m23Std 1 z))
  | 2 => (List.range 11).map (rowK (m23Std 2 z))
  | 3 => if z then m23S44aBT else m23S44aAT
  | 4 => if z then m23S44bBT else m23S44bAT
  | _ => if z then m23S120BT else m23S120AT

@[expose] noncomputable def nor23K (t : ℕ) : Bool :=
  norKP (m23Dim t) (m23Std t) (ht23 t) ((m23NorAW t).map decW) (m23NorT t)
    ((m23NorGW t).map decW) (m23NorMasks t) (m23NorPsi t) ((m23NorDW t).map decW) (m23NorR t)
    (m23NorMinv t)

end CFSG.KD.C260431
