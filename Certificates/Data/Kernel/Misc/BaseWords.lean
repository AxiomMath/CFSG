module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.Misc.BaseWords

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def evK (n w : Nat) (W : List Nat) (p : Nat) : Nat :=
  W.foldl (fun q t => nIf(Nat.blt q n, pg w (mask w) t q, 0)) p

@[expose] noncomputable def evPowK (n w : Nat) (W : List Nat) (e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => evK n w W ih) e

@[expose] noncomputable def fixBK (n w : Nat) (bs W : List Nat) (e : Nat) : Bool :=
  bs.all fun b => Nat.beq (evPowK n w W e b) b

@[expose] noncomputable def baseImgsK (n w : Nat) (bs W : List Nat) : List Nat := bs.map (evK n w W)

@[expose] noncomputable def spanAddWK (n w : Nat) (bs : List Nat) (sp : List (List Nat))
    (o : List Nat) : List (List Nat) :=
  if sp.any (fun e => baseImgsK n w bs e == baseImgsK n w bs o) then sp else sp ++ sp.map (· ++ o)

@[expose] noncomputable def spanWK (n w : Nat) (bs : List Nat) (os : List (List Nat)) :
    List (List Nat) :=
  os.foldl (spanAddWK n w bs) [[]]

@[expose] noncomputable def inSpanWK (n w : Nat) (bs : List Nat) (sp cand : List (List Nat)) :
    Bool :=
  cand.all fun x => sp.any fun e => baseImgsK n w bs e == baseImgsK n w bs x

@[expose] noncomputable def normsWK (n w : Nat) (bs B : List Nat) (g gi : Nat) : Bool :=
  inSpanWK n w bs (spanWK n w bs (B.map fun b => [b])) (B.map fun b => [gi, b, g])

end CFSG.KC.Misc.BaseWords

end
