module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem PB1_torsion_mem_iota_range
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (hinner : ∀ g ∈ I, g ^ p = 1 → g ∈ (MulAut.conj : R →* MulAut R).range)
    (z : ModGL ρ.tau Omega) (hz : z ∈ ρ.setup.D.torus) (hzp : z ^ p = 1) :
    z ∈ ρ.iota.range := by
  have hz_model : z ∈ ρ.setup.D.model := ρ.setup.D.torus_le_model hz
  let zm : ↥ρ.setup.D.model := ⟨z, hz_model⟩
  let g : MulAut R := ρ.modelAction zm
  have hgI : g ∈ I := by
    rw [← ρ.modelAction_range]
    exact ⟨zm, rfl⟩
  have hzmp : zm ^ p = 1 := by
    apply Subtype.ext
    simpa using hzp
  have hgp : g ^ p = 1 := by
    calc g ^ p = ρ.modelAction (zm ^ p) := (map_pow ρ.modelAction zm p).symm
      _ = ρ.modelAction 1 := by rw [hzmp]
      _ = 1 := map_one ρ.modelAction
  obtain ⟨r, hr⟩ := hinner g hgI hgp
  have hiota_mem : ρ.iota r ∈ ρ.setup.Γ := by
    rw [← ρ.iota_range]
    exact ⟨r, rfl⟩
  have hΓ_le : ρ.setup.Γ ≤ ρ.setup.D.model := Subgroup.commutator_le_self _
  let xm : ↥ρ.setup.D.model := ⟨ρ.iota r, hΓ_le hiota_mem⟩
  have hact : ρ.modelAction xm = MulAut.conj r := by
    ext r'
    apply ρ.iota_inj
    rw [ρ.modelAction_compat xm r', MulAut.conj_apply]
    simp only [map_mul, map_inv]
    rfl
  have hzmx : ρ.modelAction zm = ρ.modelAction xm := by
    rw [hact]
    exact hr.symm
  have hzmx_eq : zm = xm := ρ.modelAction_inj hzmx
  have hval : z = ρ.iota r :=
    congrArg (fun y : ↥ρ.setup.D.model => (y : ModGL ρ.tau Omega)) hzmx_eq
  exact ⟨r, hval.symm⟩

end CFSG.StandardType.GGK0ExcCentreU

end
