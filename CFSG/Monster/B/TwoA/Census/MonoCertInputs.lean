module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.B.TwoA.Census.SignCls
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.MonoData
public meta import CFSG.Monster.B.TwoA.Census.SignCls
public meta import CFSG.Monster.B.TwoA.Census.NatCert

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.Code

@[expose] def seedA (j : ℕ) : Array ℕ := seedArr.getD j #[]

@[expose] def ngenJ (j : ℕ) : ℕ := 12 + (centGenArrs j).length

@[expose] def actJ (j k n : ℕ) : ℕ :=
  if k < 12 then canI (n ^^^ Bmask k ^^^ permI (seedA j) (Bmask k))
  else canI (permI ((centGenArrs j).getD (k - 12) #[]) n)

@[expose] def eligB (j n : ℕ) : Bool :=
  (n ^^^ permI (seedA j) n == 0) || (n ^^^ permI (seedA j) n == OM)

@[expose] def validB (j n : ℕ) : Bool := validList.contains n && eligB j n

@[expose] def eligList (j : ℕ) : List ℕ := validList.filter (eligB j)

@[expose] def monoCert (i : ℕ) : NatCert :=
  natBfs (actJ (monoSeed.getD i 0)) (ngenJ (monoSeed.getD i 0)) (monoSign.getD i 0) 3000

end CFSG.Monster.B.TwoA.Census
