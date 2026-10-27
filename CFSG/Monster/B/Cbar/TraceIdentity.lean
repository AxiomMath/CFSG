module

public import CFSG.Monster.B.Cbar.TraceTransport
public import CFSG.Monster.B.Short.Transitivity

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity Matrix

theorem short_involution_axis_trace_identity
    (r : Q) (hr : IsShortCoord (coordOf r))
    (v : SpaceB) :
    LinearMap.trace ℚ SpaceB ((rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ gmul v) =
      bform ((1070 : ℚ) • inA oneA - (4096 : ℚ) • axis r) v := by
  obtain ⟨g, hg, hρ, ha⟩ :=
    Short.short_label_visible_transitivity.2.2.2.1 (rMinus 0 1) r hrStar hr
  exact trace_identity_transport (Generated.Gvis_le_AutO hg) hρ ha trace_rhoL_rStar v

theorem short_involution_axis_trace_identity'
    (r : Q) (hr : IsShortCoord (coordOf r))
    (v : SpaceB) :
    LinearMap.trace ℚ SpaceB (gmul v ∘ₗ (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB)) =
      bform ((1070 : ℚ) • inA oneA - (4096 : ℚ) • axis r) v := by
  rw [LinearMap.trace_comp_comm']
  exact short_involution_axis_trace_identity r hr v

end CFSG.Monster.B
