module

public import Certificates.Data.G24IdentModel

public section

namespace CFSG.Quasithin.St84.G24MF

open CFSG.Quasithin.St84.G24Ident (rho1a rho1b rho1c rhoZ1a rhoZ1b rhoZ1c rho2a rho2b rho2c
  rhoZ2a rhoZ2b rhoZ2c q1lin q1c q2lin q2c)

@[expose] def matV1 : Fin 3 → Matrix (Fin 8) (Fin 8) (ZMod 2) := ![rho1a, rho1b, rho1c]

@[expose] def matZ1 : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod 2) := ![rhoZ1a, rhoZ1b, rhoZ1c]

@[expose] def matV2 : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 2) := ![rho2a, rho2b, rho2c]

@[expose] def matZ2 : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 2) := ![rhoZ2a, rhoZ2b, rhoZ2c]

@[expose] def sqV1 (i : Fin 8) (t : Fin 2) : ZMod 2 :=
  if (q1lin.getD i.val []).getD t.val false then 1 else 0

@[expose] def cmV1 (i j : Fin 8) (t : Fin 2) : ZMod 2 :=
  if ((q1c.getD i.val []).getD j.val []).getD t.val false then 1 else 0

@[expose] def sqV2 (i : Fin 6) (t : Fin 4) : ZMod 2 :=
  if (q2lin.getD i.val []).getD t.val false then 1 else 0

@[expose] def cmV2 (i j : Fin 6) (t : Fin 4) : ZMod 2 :=
  if ((q2c.getD i.val []).getD j.val []).getD t.val false then 1 else 0

end CFSG.Quasithin.St84.G24MF
