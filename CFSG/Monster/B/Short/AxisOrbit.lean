module

public import CFSG.Monster.Generated.Centralizer
public import CFSG.Monster.Griess.AutFinite

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated

@[expose] def rStar : Q := SpinLattice.DQ (deltaPair 0 1)

@[expose] def aStar : SpaceB := axis rStar

@[expose] def tStar : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv rStar

@[expose] def axisOrbit : Set SpaceB := {a | ∃ g ∈ Gmat, g aStar = a}

@[expose] def shortClass : Set (SpaceB ≃ₗ[ℚ] SpaceB) := {t | ∃ g ∈ Gmat, g * tStar * g⁻¹ = t}

@[expose] def tAxis (a : SpaceB) : Module.End ℚ SpaceB :=
  1 - (16 / 217 : ℚ) • (gmul a * (gmul a - (4 : ℚ) • 1) * (gmul a - (16 : ℚ) • 1))

theorem rStar_eq_rMinus : rStar = rMinus 0 1 := rfl

theorem coordOf_rStar : coordOf rStar = (0, deltaPair 0 1) := coordOf_rMinus 0 1

theorem isShortCoord_rStar : IsShortCoord (coordOf rStar) :=
  isShortCoord_rMinus (by decide : (0 : Fin 24) < 1)

theorem vMinus_zero_one_mem : vMinus 0 1 ∈ minVecs := vMinus_mem (by decide : (0 : Fin 24) < 1)

theorem phi0_coordOf_rStar : phi0 (coordOf rStar) = classOf (vMinus 0 1) :=
  phi0_coordOf_rMinus (by decide : (0 : Fin 24) < 1)

theorem vMinus_zero_one : vMinus 0 1 = (4 : ℤ) • eℤ 0 - (4 : ℤ) • eℤ 1 := rfl

theorem coe_axisE_rStar : (axisE rStar : Matrix (Fin 24) (Fin 24) ℚ) = projMat (vMinus 0 1) :=
  coe_axisE_rMinus (by decide : (0 : Fin 24) < 1)

theorem aStar_eq : aStar =
    (2 : ℚ) • ((axisE rStar, 0, 0) : SpaceB) - (2 : ℚ) • ((0, Xlift rStar, 0) : SpaceB) := rfl

theorem tStar_mem_Gvis : tStar ∈ Gvis := rhoEquiv_mem_Gvis rStar

theorem tStar_mem_Gmat : tStar ∈ Gmat := Hmat_le_Gmat tStar_mem_Gvis

theorem aStar_mem_axisOrbit : aStar ∈ axisOrbit := ⟨1, one_mem _, rfl⟩

theorem tStar_mem_shortClass : tStar ∈ shortClass :=
  ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem axisOrbit_eq_range : axisOrbit = Set.range fun g : Gmat => (g : SpaceB ≃ₗ[ℚ] SpaceB) aStar := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩

theorem shortClass_eq_range :
    shortClass = Set.range fun g : Gmat => (g : SpaceB ≃ₗ[ℚ] SpaceB) * tStar * (g : _)⁻¹ := by
  ext t
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩

theorem finite_axisOrbit : axisOrbit.Finite := by
  rw [axisOrbit_eq_range]
  exact Set.finite_range _

theorem finite_shortClass : shortClass.Finite := by
  rw [shortClass_eq_range]
  exact Set.finite_range _

theorem tAxis_apply (a v : SpaceB) :
    tAxis a v = v - (16 / 217 : ℚ) •
      gmul a (gmul a (gmul a v) - (4 : ℚ) • gmul a v - (16 : ℚ) • (gmul a v - (4 : ℚ) • v)) := by
  simp only [tAxis, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sub, map_smul]

theorem concrete_axis_involution_orbit_data :
    rStar = SpinLattice.DQ (deltaPair 0 1) ∧
    deltaPair 0 1 = Submodule.Quotient.mk (Pi.single 0 1 + Pi.single 1 1) ∧
    coordOf rStar = (0, deltaPair 0 1) ∧ IsShortCoord (coordOf rStar) ∧
    vMinus 0 1 ∈ minVecs ∧ vMinus 0 1 = (4 : ℤ) • eℤ 0 - (4 : ℤ) • eℤ 1 ∧
    phi0 (coordOf rStar) = classOf (vMinus 0 1) ∧
    aStar = axis rStar ∧
    (axisE rStar : Matrix (Fin 24) (Fin 24) ℚ) = projMat (vMinus 0 1) ∧
    tStar = rhoEquiv rStar ∧ tStar ∈ Gmat ∧
    axisOrbit = {a | ∃ g ∈ Gmat, g aStar = a} ∧ axisOrbit.Finite ∧ aStar ∈ axisOrbit ∧
    shortClass = {t | ∃ g ∈ Gmat, g * tStar * g⁻¹ = t} ∧ shortClass.Finite ∧
    tStar ∈ shortClass ∧
    (∀ a : SpaceB, tAxis a =
      1 - (16 / 217 : ℚ) • (gmul a * (gmul a - (4 : ℚ) • 1) * (gmul a - (16 : ℚ) • 1))) :=
  ⟨rfl, rfl, coordOf_rStar, isShortCoord_rStar, vMinus_zero_one_mem, rfl, phi0_coordOf_rStar, rfl,
    coe_axisE_rStar, rfl, tStar_mem_Gmat, rfl, finite_axisOrbit, aStar_mem_axisOrbit, rfl,
    finite_shortClass, tStar_mem_shortClass, fun _ => rfl⟩

end CFSG.Monster.B.Short
