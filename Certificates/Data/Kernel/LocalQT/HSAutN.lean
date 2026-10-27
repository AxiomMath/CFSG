module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.HSAutN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 3850) (nat_lit 12) (mask 12) p q

@[expose] noncomputable def idn : Nat := pidn (nat_lit 3850) (nat_lit 12)

@[expose] noncomputable def img (p q : Nat) : Nat := pg (nat_lit 12) (mask 12) p q

@[expose] noncomputable def sAt (G X GI q : Nat) : Nat := img G (img X (img GI q))

@[expose] noncomputable def witK (G GI Y X p : Nat) : Bool :=
  bIf(Nat.beq (sAt G X GI (img Y p)) (img Y (sAt G X GI p)), false, true)

@[expose] noncomputable def scanK (G GI Y1 Y2 C X : Nat) : Bool :=
  bIf(witK G GI Y1 X (nat_lit 0), true, bIf(witK G GI Y1 X (nat_lit 1), true,
  bIf(witK G GI Y2 X (nat_lit 0), true, bIf(witK G GI Y2 X (nat_lit 1), true,
    strictB (pc (pc G X) GI) (fun S => bIf(Nat.beq S idn, true, Nat.beq S C))))))

@[expose] noncomputable def nPtK (A AI T PL POS SRT SRI : Nat → Nat) (G GI Y1 Y2 C cnt i : Nat) :
    Bool :=
  bAnd(penumPtK (nat_lit 3850) (nat_lit 12) (mask 12) (nat_lit 46200) false A AI (nat_lit 2) cnt
    T PL POS SRT SRI i, scanK G GI Y1 Y2 C (T i))

@[expose] noncomputable def nSlK (A AI T PL POS SRT SRI : Nat → Nat) (G GI Y1 Y2 C cnt lo len : Nat) :
    Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i cnt,
    nPtK A AI T PL POS SRT SRI G GI Y1 Y2 C cnt i, true)))

end CFSG.KS.HSAutN

end
