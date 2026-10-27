module

public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen
public import Certificates.Data.J4ZCent.Rho

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Sporadic.J4 CFSG.Quasithin.J4M2
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat (RN)
open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat (p5Gens)

@[expose] def LamP : Subgroup (Equiv.Perm (Fin 77)) := Subgroup.closure {p | p ∈ p5Phi}

@[expose] def P2 : Subgroup (Equiv.Perm (Fin 77)) := Subgroup.closure {p | p ∈ rPerms}

structure B0Facts : Prop where
  perfect : ⁅B0, B0⁆ = B0
  knorm : Kgrp ≤ Subgroup.normalizer (B0 : Set J)
  phi : ∀ g ∈ p5Gens, RN.enc (phiPerm g) = phiRN g
  closure_b0 : Subgroup.closure {p | p ∈ b0Perms} = LamP
  card_LamP : Nat.card LamP = 960
  tPerm_not : ∀ i < 60, i ≠ 0 → tPerm i ∉ P2

end CFSG.Quasithin.J4ZCent
