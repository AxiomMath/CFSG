
module

public import CFSG.Sporadic.Schreier.J4SFiveBase
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.LocalAnalysis.ComponentInitial MulAction

abbrev Xv : Type := orbit J v

instance xvFinite : Finite Xv := by
  have : Finite Row := inferInstanceAs (Finite (Fin 112 → ZMod 2))
  exact Subtype.finite

def vO : Xv := ⟨v, mem_orbit_self v⟩

theorem v_eq_rootV : v = toRow Native.rootV.toVec := by rw [v, toVecD_rootBits]

def subRep (l : ℕ) : Row :=
  (CFSG.Sporadic.J4.QT2.pathElt (CFSG.Sporadic.J4.QT2.repPaths.getD l []))⁻¹ • v

def subSizeL (l : ℕ) : ℕ :=
  [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD l 0

theorem coe_orbit_Xv (H' : Subgroup J) (x : Xv) :
    Subtype.val '' orbit H' x = orbit H' (x : Row) := by
  ext y
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, (orbit.coe_smul (m := (g : J)) (a' := x)).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g • x, ⟨g, rfl⟩, orbit.coe_smul (m := (g : J)) (a' := x)⟩

theorem ncard_orbit_Xv (H' : Subgroup J) (x : Xv) :
    (orbit H' x).ncard = (orbit H' (x : Row)).ncard := by
  rw [← coe_orbit_Xv, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem orbit_Xv_eq (H' : Subgroup J) {x y : Xv} (h : orbit H' (x : Row) = orbit H' (y : Row)) :
    orbit H' x = orbit H' y := by
  rw [← coe_orbit_Xv, ← coe_orbit_Xv] at h
  exact Set.image_injective.2 Subtype.val_injective h

end CFSG.Sporadic.J4Schreier
