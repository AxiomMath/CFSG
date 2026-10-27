module

public import Certificates.Data.Kernel.AE6Tri.DefsB

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F

@[expose] noncomputable def kcOK (G : List Nat) (DG : List (List Nat)) (KW KG CW : List (List Nat))
    (U : List (List (List Nat))) : Bool :=
  forceMap KG (fun w => awN G w) (fun KV =>
    allIx U (fun k Uk => strictB (awN G (CW.getD k [])) (fun C =>
      allIx KW (fun s w => eqN 360 9 (pmN 360 9 (awN (DG.getD k []) w) C)
        (pmN 360 9 C (awN KV (Uk.getD s [])))) 0)) 0)

end CFSG.KC.AE6Tri

end
