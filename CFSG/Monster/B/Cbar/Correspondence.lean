module

public import CFSG.Monster.B.Cbar.AxisCentral
public import CFSG.Monster.B.Short.Transitivity

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity CFSG.Monster.Generated
  CFSG.Monster.B.Short

theorem centralizer_eq_stabilizer {a : SpaceB} (ha : a ∈ axisOrbit) {t : SpaceB ≃ₗ[ℚ] SpaceB}
    (ht : (t : SpaceB →ₗ[ℚ] SpaceB) = tAxis a) :
    Gmat ⊓ Subgroup.centralizer {t} = Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) a := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff,
    LinearEquiv.smul_def]
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨hg, (commute_iff_of_eq_tAxis ha ht hg).1 hc⟩
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, (commute_iff_of_eq_tAxis ha ht hg).2 hfix⟩

theorem concrete_axis_centralizer_correspondence :
    Set.BijOn tAxis axisOrbit
      ((fun t : SpaceB ≃ₗ[ℚ] SpaceB => (t : SpaceB →ₗ[ℚ] SpaceB)) '' shortClass) ∧
    (∀ g ∈ Gmat, ∀ a ∈ axisOrbit, g a ∈ axisOrbit ∧
      tAxis (g a) = (g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ tAxis a ∘ₗ (g.symm : SpaceB →ₗ[ℚ] SpaceB)) ∧
    (∀ a ∈ axisOrbit, ∀ t ∈ shortClass, (t : SpaceB →ₗ[ℚ] SpaceB) = tAxis a →
      Gmat ⊓ Subgroup.centralizer {t} = Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) a) ∧
    (∀ r : Q, IsShortCoord (coordOf r) →
      tAxis (axis r) = (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB)) ∧
    (∀ r : Q, IsShortCoord (coordOf r) → ∀ g ∈ Gmat,
      g * rhoEquiv r = rhoEquiv r * g → g (axis r) = axis r) := by
  refine ⟨tAxis_bijOn, fun g hg a ha => ⟨apply_mem_axisOrbit hg ha,
    LinearMap.ext fun u => tAxis_AutO (Gmat_le_AutO hg) a u⟩,
    fun a ha t _ ht => centralizer_eq_stabilizer ha ht, fun r hr => tAxis_axis hr, ?_⟩
  intro r hr g hg hc
  have ha : axis r ∈ axisOrbit := short_label_visible_transitivity.2.2.2.2 r hr
  exact (commute_iff_of_eq_tAxis ha (tAxis_axis hr).symm hg).1 hc

end CFSG.Monster.B
