
module

public import CFSG.Quasithin.H13.J4FixCheckBase
public import CFSG.Quasithin.H13.J4ClassesBase
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Quasithin.H13.J4FixSpec
public import CFSG.Sporadic.Schreier.J4SLocal
public import CFSG.Sporadic.J4.Local
public import CFSG.Quasithin.H13.J4ClassCheckInputs
public import Certificates.Data.CFSGNative.H13.J4Class
public import CFSG.Sporadic.Schreier.J4SKCentBase

@[expose] public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4

abbrev Om : Type := MulAction.orbit J CFSG.Sporadic.J4Schreier.v

instance omFinite : Finite Om := by
  have : Finite Row := inferInstanceAs (Finite (Fin 112 → ZMod 2))
  exact Subtype.finite

def vOm : Om := ⟨_, MulAction.mem_orbit_self _⟩

abbrev hClass (e : J) : Set J :=
  CFSG.Sporadic.J4Schreier.conjOrbit CFSG.Sporadic.J4Schreier.H e

theorem isConj_of_mem_hClass {e s : J} (hte : IsConj tJ e) (hs : s ∈ hClass e) : IsConj tJ s := by
  obtain ⟨h, -, rfl⟩ := hs
  exact hte.trans (isConj_iff.2 ⟨h, rfl⟩)

theorem hClass_ne {e e' : J} (h : (hClass e).ncard ≠ (hClass e').ncard) : hClass e ≠ hClass e' :=
  fun e => h (by rw [e])

theorem W_subgroupOf_le_centralizer
    : W.subgroupOf J ≤ Subgroup.centralizer ({tJ} : Set J) := by
  intro w hw
  rw [Subgroup.mem_subgroupOf] at hw
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.1 (W_le_centralizer hw) t rfl

end CFSG.Quasithin.H13.J4
