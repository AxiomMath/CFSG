module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2PermData
public import Certificates.Data.CFSGNative.J4ZCent.Check

public section

namespace CFSG.Quasithin.J4ZCent

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat CFSG.Quasithin.J4M2 CFSG.Sporadic.J4.ZCent

@[expose] def b0Perm (i : ℕ) : Perm (Fin 77) :=
  ((g0W.getD i []).map fun l => sigPerm (l.toNat - 1)).prod

@[expose] def b0Perms : List (Perm (Fin 77)) := (List.range 16).map b0Perm

@[expose] def wordPerm (w : List Int) : Perm (Fin 77) :=
  (w.map fun l => if 0 < l then b0Perm (l.toNat - 1) else (b0Perm ((-l).toNat - 1))⁻¹).prod

@[expose] def rPerms : List (Perm (Fin 77)) := rW.map wordPerm

@[expose] def tPerm (i : ℕ) : Perm (Fin 77) := wordPerm (tW.getD i [])

@[expose] def phiPerm (g : Perm (Fin 22)) : Perm (Fin 77) :=
  permImg ((phiRN g).val.toList.map Fin.val)

@[expose] def p5Phi : List (Perm (Fin 77)) := p5Gens.map phiPerm

@[expose] def p5Words : List (List ℕ) := [[4, 4, 13], [15, 4, 4, 12]]

end CFSG.Quasithin.J4ZCent
