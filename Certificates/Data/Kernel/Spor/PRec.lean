module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PRec

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def wordsEqK (n w m idn : Nat) (S SI : Nat → Nat) (kS : Nat)
    (ws : List (List Int)) (G : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun wd _ ih j => bAnd(wordEqK n w m idn S SI kS wd (G j), ih (Nat.succ j))) ws (nat_lit 0)

@[expose] noncomputable def recHdK (n w m nw idn root N k : Nat) (G GI : Nat → Nat) (cnt : Nat)
    (T PL : Nat → Nat) (kS : Nat) (S SI : Nat → Nat) (ws : List (List Int)) : Bool :=
  bAnd(penumHdK root cnt N T PL, bAnd(Nat.beq cnt N, bAnd(Nat.beq k ws.length,
  bAnd(allN k (fun j => permOK n w m nw (G j) (GI j)), wordsEqK n w m idn S SI kS ws G))))

@[expose] noncomputable def centK (n w m nw k : Nat) (G : Nat → Nat) (z : Nat) : Bool :=
  allN k (fun j => commK n w m nw (G j) z)

@[expose] noncomputable def hitK (s i : Nat) (r : Nat × (Nat → Nat) × (Nat → Nat)) : Bool :=
  strictB (r32 r.2.2 i) (fun q => bAnd(Nat.blt q r.1, Nat.beq (r.2.1 q) s))

@[expose] noncomputable def anyHitK (s i : Nat) (L : List (Nat × (Nat → Nat) × (Nat → Nat))) :
    Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => bIf(hitK s i r, true, ih)) L

@[expose] noncomputable def inPairK (idn z s : Nat) : Bool :=
  bIf(Nat.beq s idn, true, Nat.beq s z)

@[expose] noncomputable def sqCoverPtK (n w m idn z : Nat) (S : Nat → Nat)
    (L : List (Nat × (Nat → Nat) × (Nat → Nat))) (i : Nat) : Bool :=
  strictB (S i) (fun s =>
    bIf(bAnd(inPairK idn z (pcomp n w m s s), bIf(inPairK idn z s, false, true)),
      anyHitK s i L, true))

@[expose] noncomputable def sqCoverK (n w m idn z : Nat) (S : Nat → Nat)
    (L : List (Nat × (Nat → Nat) × (Nat → Nat))) (cnt : Nat) : Bool :=
  allN cnt (fun i => sqCoverPtK n w m idn z S L i)

end CFSG.KS.PRec

end
