module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Lang

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem b1RatOn_one_of_geom_one {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop}
    (ha : B1aOn Omega) (hb : B1bOn Omega) (hg : B1GeomOn Omega row 1) :
    B1RatOn Omega row 1 := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hC, -⟩ := ha lab R I phi ρ j hΛ hj hqs
  obtain ⟨hHG, -⟩ := hb lab R I phi ρ j hΛ hj hqs
  have hGH : geomCentralizer ρ ≤ connectedCentralizer ρ :=
    (Subgroup.relIndex_eq_one).mp (hg lab R I phi ρ j hΛ hj hqs hrow)
  have hEq : connectedCentralizer ρ = geomCentralizer ρ := le_antisymm hHG hGH
  have hconn : conn ρ = centralizerGroup ρ := by
    rw [conn, hEq]
    exact hC.symm
  rw [hconn]
  exact Subgroup.relIndex_self (centralizerGroup ρ)

end CFSG.StandardType.S2MathAs1E6Companion1625

end
