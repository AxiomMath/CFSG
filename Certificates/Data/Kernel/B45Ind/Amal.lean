module

public import Certificates.Data.Kernel.B45Ind.Defs
public import Certificates.Data.Kernel.F2Rank34.Defs
public import Certificates.Data.SmithB45MatIndAmal

public section

namespace CFSG.KC.B45Ind

open CFSG.Quasithin.B45Mat.Ind CFSG.Quasithin.B45Mat.M22 CFSG.Quasithin.H.Mathieu
  CFSG.QuasithinUnique.Setup.X3E CFSG.KC.F2R34

@[expose] def psiL (g : Equiv.Perm (Fin 22)) : List ℕ :=
  let gl := List.ofFn fun i : Fin 22 => (g i : ℕ)
  (List.range 24).map fun m =>
    if m < 2 then m else jCatArr.toList.getD (gl.getD (jInvArr.toList.getD m 0) 0) 0

@[expose] def rows10L (a : List ℕ) : List ℕ :=
  (List.range 10).map fun i => ofBits 10 fun j => (actC10 a.toArray (2 ^ j)).testBit i

@[expose] def rows34L (tR : List ℕ) : List ℕ :=
  (List.range 34).map fun i =>
    xorSel 100 (xK tR (xorSel 34 (2 ^ i) fun l => P34Rows.getD l 0)) fun l => B34Rows.getD l 0

@[expose] def cols34L (g : Equiv.Perm (Fin 22)) : List ℕ :=
  let R := rows34L (rows10L (psiL g))
  (List.range 34).map fun j => ofBits 34 fun i => (R.getD i 0).testBit j

@[expose] def amalRelL : Bool :=
  let a := psiL (CFSG.Sporadic.Mathieu.m22a : Equiv.Perm (Fin 22))
  let b := psiL (CFSG.Sporadic.Mathieu.m22b : Equiv.Perm (Fin 22))
  [(amalH1, amalHP1), (amalH2, amalHP2)].all fun p =>
    comp24L m23AArr.toList (wordL a b (decW p.2)) == comp24L (wordL a b (decW p.1)) m23AArr.toList

@[expose] def amalOKL : Bool :=
  amalRelL && amalCore (cols34L (CFSG.Sporadic.Mathieu.m22a : Equiv.Perm (Fin 22)))
    (cols34L (CFSG.Sporadic.Mathieu.m22b : Equiv.Perm (Fin 22)))

end CFSG.KC.B45Ind
