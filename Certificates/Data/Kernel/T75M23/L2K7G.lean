module

public import Certificates.Data.Kernel.T75M23.L2K7F

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23

@[expose] noncomputable def swCj7 (A T B0 B1 : Nat) (S : List Nat) (U : Nat) (R T16 : List Nat) :
    Bool :=
  inDS A T B0 B1 S && inSAtI A T B0 S && inSAtI A T B1 S && R.any (fun Y => conjAt A T U Y) &&
    strictB (pc A T) fun G => forceL (fun Y => pc Y G) T16 fun TG =>
      T16.all fun X => strictB (pc G X) fun Q => TG.any fun Z => eqP Q Z

@[expose] noncomputable def swConjK (L : Int → Nat) (s2 reps cw : List Nat) : Bool :=
  reps.all (fun r => Nat.blt r 40320) &&
    withL L fun L =>
      strictB (pw L (bGen7 0)) fun B0 => strictB (pw L (bGen7 1)) fun B1 =>
      strictB (pw L (bGen7 0 ++ bGen7 1)) fun B01 =>
      eqP (pc B0 B0) idn && eqP (pc B1 B1) idn && eqP (pc B1 B0) B01 &&
      forceL (el L) reps fun R => forceL (tk L) (List.range 16) fun T16 =>
        zipAll 0 (fun c j => swCj7 (ak L (j / 16)) (tk L (j % 16)) B0 B1 [idn, B0, B1, B01]
          (el L c) R T16) s2 cw

end CFSG.KC.N7K

end
