module

public import Certificates.Data.Kernel.L34W.Tab42
public import Certificates.Data.Kernel.L34K
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGraphCertInputs

public section

namespace CFSG.KC.L34Graph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def forceL (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => strictB x fun x' => ih fun l => k (x' :: l)) l k

@[expose] noncomputable def pxK (G : Nat → Nat) (κ : Nat) : List Nat :=
  (List.range 16).flatMap fun k => ((List.range 16).filter (xc κ k)).map fun m =>
    pcomp 42 6 (mask 6) (tgK G k) (tgK G (4 * m))

@[expose] noncomputable def decK (G : Nat → Nat) : Bool :=
  forceL ((List.range 16).map (tgK G)) fun A =>
  forceL ((List.range 16).map fun m => tgK G (4 * m)) fun B =>
    allN 64 fun k => strictB (tgK G k) fun t =>
      A.any fun a => B.any fun b => Nat.beq (pcomp 42 6 (mask 6) a b) t

@[expose] noncomputable def invK (z4 z8 : Nat) (X : List (List Nat)) (ρ : Nat) : Bool :=
  CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (commPt 42 6 ρ z4) (commPt 42 6 ρ z8)))
    (X.all fun L => L.all fun x => strictB (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) ρ x) ρ) fun y =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (L.any fun v => Nat.beq v y)) (Nat.beq (pcomp 42 6 (mask 6) y x) (pidn 42 6)))

@[expose] noncomputable def graphK (G T1 T2 T3 : Nat → Nat) : Bool :=
  strictB (tgK G 4) fun z4 => strictB (tgK G 8) fun z8 =>
  forceL (pxK G 0) fun X0 => forceL (pxK G 1) fun X1 => forceL (pxK G 2) fun X2 =>
    CFSG.KLie.CT.andB (allN 360 fun i => strictB (T1 i) (invK z4 z8 [X0, X1, X2]))
      (CFSG.KLie.CT.andB (allN 1008 fun i => strictB (T2 i) (invK z4 z8 [X0, X1, X2]))
        (allN 280 fun i => strictB (T3 i) (invK z4 z8 [X0, X1, X2])))

end CFSG.KC.L34Graph

end
