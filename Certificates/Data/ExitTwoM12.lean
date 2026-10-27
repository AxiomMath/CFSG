module

public import Certificates.Data.M163M12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution.Q3.TL4.MF163

@[expose] def wI0 : List ℤ :=
  [-2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, -2]

@[expose] def wJ0 : List ℤ :=
  [2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1,
    -2, 1, 2]

@[expose] def wI1 : List ℤ :=
  [2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1,
    -2, 1, 2]

@[expose] def wJ1 : List ℤ :=
  [2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2,
    1, 2]

@[expose] def wG : List ℤ :=
  [2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def q8List (i j : Equiv.Perm (Fin 12)) : List (Equiv.Perm (Fin 12)) :=
  [1, i, i * i, i * i * i, j, i * j, i * i * j, i * i * i * j]

@[expose] def quatL0 (_ : Unit) : List (Equiv.Perm (Fin 12)) :=
  q8List (evalCodes [m12gA, m12gB] wI0) (evalCodes [m12gA, m12gB] wJ0)

@[expose] def quatL1 (_ : Unit) : List (Equiv.Perm (Fin 12)) :=
  q8List (evalCodes [m12gA, m12gB] wI1) (evalCodes [m12gA, m12gB] wJ1)

@[expose] def betaL0 (_ : Unit) : List (Equiv.Perm (Fin 12)) :=
  q8List (evalCodes [m12gA, m12bp] wI0) (evalCodes [m12gA, m12bp] wJ0)

@[expose] def betaL1 (_ : Unit) : List (Equiv.Perm (Fin 12)) :=
  q8List (evalCodes [m12gA, m12bp] wI1) (evalCodes [m12gA, m12bp] wJ1)

@[expose] def witU (_ : Unit) : Equiv.Perm (Fin 12) :=
  evalCodes [m12gA, m12gB] wG * (quatL1 ()).getD 7 1 * (evalCodes [m12gA, m12gB] wG)⁻¹

@[expose] def witV (_ : Unit) : Equiv.Perm (Fin 12) :=
  evalCodes [m12gA, m12gB] wG * (quatL1 ()).getD 6 1 * (evalCodes [m12gA, m12gB] wG)⁻¹

@[expose] def chkMemC (_ : Unit) : Bool :=
  (quatL0 () ++ quatL1 ()).all fun x => decide (x ∈ enumerationTab m12CentQ1)

@[expose] def chkClosed (_ : Unit) : Bool :=
  ((quatL0 ()).all fun a => (quatL0 ()).all fun b => decide (a * b ∈ quatL0 ())) &&
  ((quatL1 ()).all fun a => (quatL1 ()).all fun b => decide (a * b ∈ quatL1 ())) &&
  ((quatL0 ()).all fun a => decide (a⁻¹ ∈ quatL0 ())) &&
  ((quatL1 ()).all fun a => decide (a⁻¹ ∈ quatL1 ()))

@[expose] def chkRoots (_ : Unit) : Bool :=
  m12SqRoots1.all fun x => (decide (x ∈ quatL0 ()) || decide (x ∈ quatL1 ())) &&
    m12SqRoots1.all fun y => decide (x * y = y * x) ||
      (decide (x ∈ quatL0 ()) && decide (y ∈ quatL0 ())) ||
      (decide (x ∈ quatL1 ()) && decide (y ∈ quatL1 ()))

@[expose] def chkNorm (_ : Unit) : Bool :=
  (enumerationTab m12CentQ1).all fun g =>
    ((quatL0 ()).all fun a => decide (g * a * g⁻¹ ∈ quatL0 ())) &&
    (quatL1 ()).all fun a => decide (g * a * g⁻¹ ∈ quatL1 ())

@[expose] def chkBeta (_ : Unit) : Bool :=
  ((betaL0 ()).all fun x => decide (x ∈ quatL1 ())) &&
  (betaL1 ()).all fun x => decide (x ∈ quatL0 ())

@[expose] def chkWit (_ : Unit) : Bool :=
  !decide (witU () = 1) && !decide (witU () * witU () = 1) &&
  ((quatL0 ()).all fun a => decide (witU () * a * (witU ())⁻¹ ∈ quatL0 ())) &&
  !((quatL0 ()).all fun a => decide (witV () * a * (witV ())⁻¹ ∈ quatL0 ()))

@[expose] def chkMeet (_ : Unit) : Bool :=
  ((quatL0 ()).all fun a => !decide (a ∈ quatL1 ()) || decide (a = 1) || decide (a = m12Rep1)) &&
  decide ((quatL0 ()).getD 2 1 = m12Rep1) && decide ((quatL1 ()).getD 2 1 = m12Rep1)

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12
