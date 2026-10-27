module

public import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Schreier.M11Data

public section

namespace CFSG.Sporadic.Schreier.M11Sylow

open CFSG.Sporadic.Mathieu

@[expose] def pU (_ : Unit := ()) : Equiv.Perm (Fin 11) :=
  m11gA * m11gB⁻¹ * m11gA * m11gB * m11gA * m11gB * m11gB

@[expose] def pV (_ : Unit := ()) : Equiv.Perm (Fin 11) := m11gB * pU () * m11gB⁻¹

@[expose] def pE (_ : Unit := ()) : List (Equiv.Perm (Fin 11)) :=
  let u := pU ()
  let v := pV ()
  [1, u, u ^ 2, v, u * v, u ^ 2 * v, v ^ 2, u * v ^ 2, u ^ 2 * v ^ 2]

@[expose] def p0 : Fin 11 := 6

@[expose] def q0 : Fin 11 := 10

@[expose] def centCheck (_ : Unit := ()) : Bool :=
  let u := pU ()
  let v := pV ()
  let E := pE ()
  m11Elements.all fun g => !(decide (g * u = u * g) && decide (g * v = v * g)) || E.contains g

@[expose] def cent18Check (_ : Unit := ()) : Bool :=
  let E := pE ()
  let els := m11Elements
  E.all fun e => decide (e = 1) || (els.filter fun g => decide (g * e = e * g)).length == 18

@[expose] def moveCheck (_ : Unit := ()) : Bool :=
  m11Elements.all fun g => !(orderIs g 5 || orderIs g 11) ||
    ((g p0 != p0 && g p0 != q0) || (g q0 != p0 && g q0 != q0))

end CFSG.Sporadic.Schreier.M11Sylow
