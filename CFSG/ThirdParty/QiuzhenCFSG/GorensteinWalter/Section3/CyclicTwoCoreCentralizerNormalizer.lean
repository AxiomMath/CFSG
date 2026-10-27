module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreCentralizerT1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerControl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCoreInfra
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: conditional centralizer-to-coatom reduction

The corrected `P ∨ P^g` witness proves that `B` normalizes a nontrivial
subgroup of `B ∩ M`, but it does not prove the paper's stronger assertion
that `C_U(t₁)` normalizes the same subgroup.  This module isolates the exact
remaining reduction that is valid once the natural missing leg
`C_U(t₁) ≤ N_G(B)` is supplied: the landed A₇ layer-transfer theorem applied
to `X = B` gives `N_G(B) ≤ M`, hence `C_U(t₁) ≤ M`.

No source normality claim about `B ∩ P P^g` is used.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic first-case A₇ layer model, the missing centralizer
containment follows from the natural normalizer leg `C_U(t₁) ≤ N_G(B)`.

The proof takes `X = B` in the already proved A₇ layer-transfer and coatom
normalizer-control theorems.  The hypotheses `B ≤ M` and `B ≠ ⊥` ensure that
`B` is a valid nontrivial subgroup of `B ∩ M` for that transfer.
-/
public theorem firstCase_cyclic_centralizer_t1_le_M_of_normalizes_B_of_a7
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
    (hp3 : od.p = 3)
    (hCnormB : centralizerIn od.d.bg.U od.d.bg.t1 ≤
      Subgroup.normalizer (od.d.bg.B : Set G)) :
    centralizerIn od.d.bg.U od.d.bg.t1 ≤ M := by
  have hBne : od.d.bg.B ≠ ⊥ :=
    firstCase_cyclic_B_ne_bot hmin c od hfirst hHhat hU Q
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hBleBM : od.d.bg.B ≤ od.d.bg.B ⊓ M := by
    exact le_inf le_rfl hBleM
  have hEeq :
      componentLayerOf (Subgroup.normalizer
        (od.d.bg.B : Set G)) = componentLayerOf M :=
    firstCase_cyclic_componentLayer_normalizer_eq_of_a7
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7
      od.d.bg.B hBne hBleBM
  have hNleM : Subgroup.normalizer (od.d.bg.B : Set G) ≤ M :=
    firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7
      od.d.bg.B hBne hBleBM hEeq
  exact hCnormB.trans hNleM

end CFSG.GorensteinWalter
