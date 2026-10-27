module

public import Certificates.Data.Kernel.B45Nor.Defs
public import Certificates.Data.SmithB45MatIndM24Nor
public import Certificates.Kernel.C260433.Data

public section

namespace CFSG.KD.C260433

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

@[expose] noncomputable def ht24 (t : ℕ) (z : Bool) : List ℕ :=
  match t with
  | 1 => (List.range 11).map (rowK (m24Std 1 z))
  | 2 => (List.range 11).map (rowK (m24Std 2 z))
  | 3 => if z then m24S44aBT else m24S44aAT
  | 4 => if z then m24S44bBT else m24S44bAT
  | _ => if z then m24S120BT else m24S120AT

@[expose] noncomputable def nor24K (t : ℕ) : Bool :=
  norKP (m24Dim t) (m24Std t) (ht24 t) ((m24NorAW t).map decW) (m24NorT t)
    ((m24NorGW t).map decW) (m24NorMasks t) (m24NorPsi t) ((m24NorDW t).map decW) (m24NorR t)
    (m24NorMinv t)

end CFSG.KD.C260433
