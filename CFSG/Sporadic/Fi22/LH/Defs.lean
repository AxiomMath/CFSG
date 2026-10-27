module

public import CFSG.Sporadic.Fi22.Nfp
public import Certificates.Data.CFSGNative.Fi22.LHData

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def lhRoot
    (i : Fin 2) : Set D := ptD '' {k | k.val ∈ lhData[i.val]!}

@[expose] def lhOrbit (i : Fin 2) : Set (Set D) :=
  {T | ∃ g : J, T = ⇑(Pair.conjPerm pair_D g) '' lhRoot i}

theorem lhRoot_mem_lhOrbit (i : Fin 2) : lhRoot i ∈ lhOrbit i :=
  ⟨1, by rw [map_one, Equiv.Perm.coe_one, Set.image_id]⟩

@[expose] def xi23Root :
    lhOrbit 0 := ⟨lhRoot 0, lhRoot_mem_lhOrbit 0⟩

@[expose] noncomputable def lhU :
    Equiv.Perm D := ptD.symm.trans (uOut.trans ptD)

theorem lhU_apply
    (i : Fin 3510) : lhU (ptD i) = ptD (uOut i) := by
  simp [lhU]

end CFSG.Sporadic.Fi22
