module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFamily
public import CFSG.LocalAnalysis.StandardType.GGComponentOfSSup
public import CFSG.LocalAnalysis.StandardType.GGSubgroupOfSSup

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem GGA6CharTwoLie.of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : GGA6CharTwoLie J) : GGA6CharTwoLie J' := by
  obtain ⟨t, k, d, hm⟩ := h
  exact ⟨t, k, d, hm.of_mulEquiv (QuotientGroup.congr (Subgroup.center J) (Subgroup.center J') e
    (Subgroup.map_center_eq e))⟩

theorem ggA6_isComponentOf_subgroupOf_top {G : Type} [Group G] {C J : Subgroup G}
    (hJ : IsComponentOf J C) : IsComponentOf (J.subgroupOf C) (⊤ : Subgroup ↥C) := by
  have h0 : CFSG.Open.IsComponentOf (J.subgroupOf C) (⊤ : Subgroup ↥C) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.top_iff.mpr (IsSubnormal.subgroupOf hJ.2.1)
    · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.2
  exact CFSG.Assembly.isComponentOf_iff_open.2 h0

theorem isComponentOf_of_isCoreFamily {G : Type} [Group G] {C : Subgroup G}
    {β : Type} {S : β → Subgroup G} (hS : LayerCores.IsCoreFamily C S) (c : β) :
    IsComponentOf (S c) C := by
  refine ⟨hS.1 c, ?_, (TableBSymp.isQuasisimple_iff (S c)).mpr (hS.2.2.1 c)⟩
  refine IsSubnormal.step (hS.1 c) ?_ (IsSubnormal.refl C)
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hS.2.1 c g g.2 x hx

theorem GGA6CharTwoLie_of_isCoreFamily {G : Type} [Group G] [Finite G]
    {C : Subgroup G} {β : Type} {S : β → Subgroup G}
    (hS : LayerCores.IsCoreFamily C S) (hshape : ∀ c, GGA6CharTwoLie ↥(S c))
    {J : Subgroup G} (hJ : IsComponentOf J C) : GGA6CharTwoLie ↥J := by
  classical
  have hS1 : LayerCores.IsCoreFamily C S := hS
  obtain ⟨hSC, hSn, hSq, ⟨k, hk⟩, _hZ⟩ := hS
  have hJq : CFSG.IsQuasisimple J := (TableBSymp.isQuasisimple_iff J).mp hJ.2.2
  have hJperf : ⁅J, J⁆ = J := LayerFacts.ggCommutator_eq_of_isQuasisimple hJq
  have hJle : J ≤ sSup (Set.range S) := by
    calc J = LayerFacts.ggDer J k := (LayerFacts.ggDer_of_perfect hJperf k).symm
      _ ≤ LayerFacts.ggDer C k := LayerFacts.ggDer_mono hJ.1 k
      _ ≤ ⨆ c, S c := hk
  have hle : J.subgroupOf C ≤ sSup ((fun a => a.subgroupOf C) '' Set.range S) := by
    have h := map_subgroupOf_sSup (H := C) (f := MonoidHom.id ↥C) (𝒞 := Set.range S)
      (by rintro _ ⟨c, rfl⟩; exact hSC c)
    have h' : (sSup (Set.range S)).subgroupOf C =
        sSup ((fun a => a.subgroupOf C) '' Set.range S) := by
      simpa only [Subgroup.map_id] using h
    rw [← h']
    exact Subgroup.comap_mono (f := C.subtype) hJle
  obtain ⟨D, hD, hDc⟩ := isComponentOf_mem_of_le_sSup (ggA6_isComponentOf_subgroupOf_top hJ)
    (by
      rintro D ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := hx
      exact ggA6_isComponentOf_subgroupOf_top (isComponentOf_of_isCoreFamily hS1 c))
    hle
  obtain ⟨c, rfl⟩ := hD
  have hJeq : J = S c := by
    have hmap := congrArg (Subgroup.map C.subtype) hDc.symm
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ.1,
      Subgroup.map_subgroupOf_eq_of_le (hSC c)] at hmap
  exact GGA6CharTwoLie.of_mulEquiv (MulEquiv.subgroupCongr hJeq).symm (hshape c)

end CFSG.StandardType.A6Red

end
