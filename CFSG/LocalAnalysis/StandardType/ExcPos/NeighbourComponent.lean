module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent
import CFSG.LocalAnalysis.StandardType.ExcPos.PacketBasic
import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentSelect
import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentOrbit
import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentPacket
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem excUK_holds :
    ExcUK := by
  intro t ht X _ _ n f ψ p G₀ B₁ D J L x hH R Rm P e he he1 K hKG hK hJK hZ
  obtain ⟨hp, hp2, hDB, hJ⟩ := ggSixPosHyp_excUK_facts hH
  have hker : kernelRoots P.chiD ⊆ kernelRoots (P.chiAt e) :=
    P.kernelRoots_chiD_subset hDB he
  let iK : KernelComponent (P.chiAt e) := containingComponent hker P.iJ
  have hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK :=
    componentRoots_subset_containingComponent hker P.iJ
  have hJi : (J.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
      (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) :=
    P.map_J_le.trans (rootSpan_mono (ratOrbit_mono P.ρ hsub))
  have hJK' : (J.subgroupOf G₀).map P.η ≤ (K.subgroupOf G₀).map P.η :=
    Subgroup.map_mono (Subgroup.comap_mono hJK)
  have hK' : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map P.η)
      (P.Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit (GGFinModel.langTag t) (P.coord e)}) :=
    P.attach_nbr e he K hKG hK
  obtain ⟨j, hj⟩ := exists_component_le_ratOrbitSpan_single P.Δ P.ρ P.frob P.finite hp hp2
    (P.coord e) (P.coord_torus e he) (P.rootDiagUnit_coord_pow he) _ hK'
  have horbit : LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK) =
      LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) j) :=
    ratOrbit_eq_of_isQuasisimple_le (fun γ hγ => P.mapsTo_rho_chiAt he hγ)
      P.frob.iform_eq P.attach_J.2.2 hJi (hJK'.trans hj)
  have hKle : (K.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
      (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) := by
    rw [horbit]
    exact hj
  exact ⟨iK, hsub, hKle, fun heq =>
    P.eq_J_of_map_le_rootSpan_rootsJ hDB hJ he hKG hK hJK (by rwa [heq] at hKle)⟩

end CFSG.StandardType.LieKnownR2.ExcPos

end
