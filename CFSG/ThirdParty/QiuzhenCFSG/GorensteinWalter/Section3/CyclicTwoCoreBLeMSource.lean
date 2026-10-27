module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreSourceNormalizerWitness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerControl
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: `B ≤ M` in the cyclic first-case A₇ layer model — corrected source assembly

This module assembles the corrected source paragraph (p. 223) proof of
`B ≤ M` from the three landed APIs:

1. `firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M`
   supplies `X ≠ ⊥` with `X ≤ B ∩ M` and `B ≤ N_G(X)`;
2. `firstCase_cyclic_componentLayer_normalizer_eq_of_a7` gives
   `E(N_G(X)) = E(M)`;
3. `firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq`
   gives `N_G(X) ≤ M`.

The conclusion `B ≤ M` is the composition `B ≤ N_G(X) ≤ M`.
No `sorry`, `admit`, `axiom`, or `opaque` is used.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic first-case A₇ layer model, `B ≤ M`.

The witness `X` is the nontrivial `B ∩ M`-subgroup produced by the corrected
`PP^g` normalizer argument; the A₇ layer transfer then gives
`E(N_G(X)) = E(M)`, and the coatom normalizer-control leg gives
`N_G(X) ≤ M`. -/
public theorem firstCase_cyclic_B_le_M_of_a7_source
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
    od.d.bg.B ≤ M := by
  obtain ⟨X, hXne, hXle, hBnorm, _⟩ :=
    firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hEeq :
      componentLayerOf (Subgroup.normalizer (X : Set G)) =
        componentLayerOf M :=
    firstCase_cyclic_componentLayer_normalizer_eq_of_a7
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hXne hXle
  have hNXleM : Subgroup.normalizer (X : Set G) ≤ M :=
    firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hXne hXle hEeq
  exact hBnorm.trans hNXleM

end CFSG.GorensteinWalter
