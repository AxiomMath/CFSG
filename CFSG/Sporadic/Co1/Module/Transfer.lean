module

public import CFSG.Monster.Existence.Co1Bridge
public import CFSG.Sporadic.Co1.Module.Orbits

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Monster.Existence.Co1Bridge CFSG.Blueprint Matrix

theorem J_eq_closure_gen (D : SmallF2.Native.VecData) : SmallF2.J D = Subgroup.closure
    {((SmallF2.a D : SmallF2.J D) : GL (Fin D.d) (ZMod 2)),
      ((SmallF2.b D : SmallF2.J D) : GL (Fin D.d) (ZMod 2))} := rfl

theorem matA_eq_aMat : matA = aMat := by
  rw [aMat_def]
  rfl

theorem matB_eq_bMat : matB = bMat := by
  rw [bMat_def]
  rfl

theorem gA24_eq :
    gA24 = (genA : GL (Fin 24) (ZMod 2)) :=
  Units.ext (by rw [genA_val, matA_eq_aMat]; rfl)

theorem gB24_eq :
    gB24 = (genB : GL (Fin 24) (ZMod 2)) :=
  Units.ext (by rw [genB_val, matB_eq_bMat]; rfl)

theorem Jmat_eq_J24 : Jmat = J24 := by
  have h : Jmat = Subgroup.closure
      {(genA : GL (Fin 24) (ZMod 2)), (genB : GL (Fin 24) (ZMod 2))} := J_eq_closure_gen dat
  rw [h, J24, gA24_eq, gB24_eq]

theorem J24_orbit_ncard_v₂ :
    (MulAction.orbit J24 v₂).ncard = 98280 := by
  rw [← Jmat_eq_J24]
  exact orbit_ncard_v₂

theorem J24_orbit_ncard_v₃ :
    (MulAction.orbit J24 v₃).ncard = 8386560 := by
  rw [← Jmat_eq_J24]
  exact orbit_ncard_v₃

theorem J24_orbit_ncard_v₄ :
    (MulAction.orbit J24 v₄).ncard = 8292375 := by
  rw [← Jmat_eq_J24]
  exact orbit_ncard_v₄

theorem J24_exists_unique_orbit
    {v : Vec24} (hv : v ≠ 0) :
    ∃! i : Fin 3, v ∈ MulAction.orbit J24 (reps i) := by
  rw [← Jmat_eq_J24]
  exact exists_unique_orbit hv

end CFSG.Sporadic.Co1.Module
