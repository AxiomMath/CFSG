module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBLeMSource
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: normalizing the odd-core intersection

After the corrected A₇-layer argument gives `B ≤ M` and
`B ∩ M = O₂′(M)`, the subgroup `B ∩ M` is normalized by `B`: it is the image
of the normal subgroup `O₂′(M)` under the subgroup inclusion `M ≤ G`.
This is the exact normalizer leg needed before attempting the remaining
centralizer containment `C_U(t₁) ≤ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic first-case A₇ layer model, `B` normalizes `B ∩ M`.

The proof uses only the landed identities `B ≤ M` and
`B ∩ M = (pPrimeCore 2 M).map M.subtype`; no claim about the invalid
`B ∩ P P^g` witness is used.
-/
public theorem firstCase_cyclic_B_normalizes_inter_of_a7_source
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3) :
    od.d.bg.B ≤ Subgroup.normalizer
      ((od.d.bg.B ⊓ M : Subgroup G) : Set G) := by
  classical
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hBMeq : od.d.bg.B ⊓ M = (pPrimeCore 2 M).map M.subtype :=
    firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hBMeq] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxM, hxEq⟩
    let bM : M := ⟨b, hBleM hb⟩
    have hxEq' : (xM : G) = x := by simpa using hxEq
    have hconjM : bM * xM * bM⁻¹ ∈ pPrimeCore 2 M :=
      (pPrimeCore_normal (p := 2) (G := M)).conj_mem xM hxM bM
    refine Subgroup.mem_map.mpr ⟨bM * xM * bM⁻¹, hconjM, ?_⟩
    change b * (xM : G) * b⁻¹ = b * x * b⁻¹
    rw [hxEq']
  · intro hx
    rw [hBMeq] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxM, hxEq⟩
    let bM : M := ⟨b, hBleM hb⟩
    have hxEq' : (xM : G) = b * x * b⁻¹ := by simpa using hxEq
    have hconjM : bM⁻¹ * xM * bM ∈ pPrimeCore 2 M := by
      simpa using (pPrimeCore_normal (p := 2) (G := M)).conj_mem xM hxM bM⁻¹
    refine Subgroup.mem_map.mpr ⟨bM⁻¹ * xM * bM, hconjM, ?_⟩
    change b⁻¹ * (xM : G) * b = x
    rw [hxEq']
    group

end CFSG.GorensteinWalter
