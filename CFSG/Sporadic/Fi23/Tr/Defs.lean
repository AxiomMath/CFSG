module

public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Fischer.Pairs
public import Certificates.Data.CFSGNative.Fi23.TrData

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_orbit_iff_isConj
    (x : J) : x ∈ MulAction.orbit (ConjAct J) d ↔ IsConj d x := by
  rw [isConj_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.ofConjAct g, by rw [ConjAct.smul_def]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, by rw [toConjAct_smul_eq]⟩

@[expose] noncomputable def ptD23 : Fin 31671 ≃ D23 :=
  ptEquiv.trans (Equiv.subtypeEquivRight mem_orbit_iff_isConj)

theorem ptD23_val
    (i : Fin 31671) : (ptD23 i : J) = conjPt i.val := rfl

@[expose] noncomputable def trRoot :
    Set D23 := ptD23 '' {k | k.val ∈ trData}

@[expose] def trOrbit : Set (Set D23) :=
  {T | ∃ g : J, T = ⇑(Pair.conjPerm pair_J g) '' trRoot}

theorem trRoot_mem_trOrbit : trRoot ∈ trOrbit :=
  ⟨1, by rw [map_one, Equiv.Perm.coe_one, Set.image_id]⟩

@[expose] noncomputable def xi24Root :
    trOrbit := ⟨trRoot, trRoot_mem_trOrbit⟩

@[expose] noncomputable def cRoot :
    Set D23 := ptD23 '' {k | k.val ∈ cData}

@[expose] def cOrbit : Set (Set D23) :=
  {T | ∃ g : J, T = ⇑(Pair.conjPerm pair_J g) '' cRoot}

theorem cRoot_mem_cOrbit : cRoot ∈ cOrbit :=
  ⟨1, by rw [map_one, Equiv.Perm.coe_one, Set.image_id]⟩

end CFSG.Sporadic.Fi23
