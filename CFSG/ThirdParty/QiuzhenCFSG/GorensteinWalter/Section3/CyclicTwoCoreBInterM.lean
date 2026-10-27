module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreOddCoreInB
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The full `B ∩ M = O(M)` equality in the A₇ layer model

The reverse containment `O(M) ≤ B` is supplied by
`firstCase_cyclic_oddCore_le_B_of_a7_layer`.  For the forward containment,
the quotient image of the Sylow `2`-subgroup `S` under
`M / O(M) ≃ A₇` is a Sylow `2`-subgroup of `A₇`; the existing
`firstCase_cyclic_B_inter_M_le_oddCore_of_a7model` then applies.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic first-case A₇ layer model, `B ∩ M` is exactly the odd
core of the maximal overgroup `M`. -/
public theorem firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B) :
    od.d.bg.B ⊓ M = (pPrimeCore 2 M).map M.subtype := by
  classical
  let O0 : Subgroup M := pPrimeCore 2 M
  let O : Subgroup G := O0.map M.subtype
  let : O0.Normal := pPrimeCore_normal
  let q : M →* M ⧸ O0 := QuotientGroup.mk' O0
  let SM : Sylow 2 M := c.S.subtype hSM
  let SQ : Sylow 2 (M ⧸ O0) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective O0) SM
  obtain ⟨eM⟩ := firstCase_cyclic_m_quotient_a7_of_layer_a7
    hmin M hMmax hA7
  let eA : Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7)) := ⟨eM⟩
  let SA : Sylow 2 (alternatingGroup (Fin 7)) :=
    Sylow.mapSurjective (f := eA.some.toMonoidHom) eA.some.surjective SQ
  have hSbar : ((c.S : Subgroup G).subgroupOf M).map
      (eA.some.toMonoidHom.comp q) = (SA : Subgroup (alternatingGroup (Fin 7))) := by
    have hSMco : (SM : Subgroup M) = (c.S : Subgroup G).subgroupOf M := by
      exact Sylow.coe_subtype c.S hSM
    have hSQco : (SQ : Subgroup (M ⧸ O0)) = (SM : Subgroup M).map q := by
      exact (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective O0) SM).symm
    have hSAco : (SA : Subgroup (alternatingGroup (Fin 7))) =
        (SQ : Subgroup (M ⧸ O0)).map eA.some.toMonoidHom := by
      exact (Sylow.coe_mapSurjective (f := eA.some.toMonoidHom)
        eA.some.surjective SQ).symm
    rw [hSAco, hSQco, hSMco, Subgroup.map_map]
  have hfwd := firstCase_cyclic_B_inter_M_le_oddCore_of_a7model
    c od hU M hSM eA SA hSbar
  have hrev := firstCase_cyclic_oddCore_le_B_of_a7_layer
    hmin c od M hMmax hSM fd hV2 hA7
  apply le_antisymm hfwd
  intro x hx
  have hxO : x ∈ O := hx
  have hxB : x ∈ od.d.bg.B := hrev hxO
  have hxM : x ∈ M := Subgroup.map_subtype_le (H := M) (pPrimeCore 2 M) hxO
  exact Subgroup.mem_inf.mpr ⟨hxB, hxM⟩

end CFSG.GorensteinWalter
