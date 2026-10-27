module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBInterM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: A₇-layer normalizer control — reduction to the layer equality

The source paragraph (p. 223) needs
`componentLayerOf (N_G(X)) = componentLayerOf M` for every nontrivial
`X ≤ B ∩ M`.  This module records the fully proved coatom leg: once that
equality holds, `N_G(X) ≤ N_G(E(M)) = M`.

The forward half `componentLayerOf M ≤ componentLayerOf (N_G(X))` follows
from Lemma 2.9 plus the A₇ quotient, but the reverse half requires a
D-group layer-transfer statement that is not present in the Section-2
component transport infrastructure.  The exact missing core is recorded in
`/tmp/s3-source-normalizer-report.md`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The coatom normalizer-control leg of the Section-3 A₇ layer paragraph:
once the component layer of `N_G(X)` equals the component layer of the
maximal overgroup `M`, the normalizer lies in `M`. -/
public theorem firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ od.d.bg.B ⊓ M)
    (hEeq : componentLayerOf (Subgroup.normalizer (X : Set G)) =
      componentLayerOf M) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  classical
  let E : Subgroup G := componentLayerOf M
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hV2ne : fd.V2 ≠ ⊥ := by
      intro hVbot
      have hcard : Nat.card fd.V2 = 4 := fd.V2_klein.card_four
      rw [hVbot] at hcard
      norm_num at hcard
    apply hV2ne
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mp (by simpa [E, hbot] using hV2 hx)
  have hE_normal_N : IsNormalIn E N := by
    simpa [E, ← hEeq] using (componentLayerOf_isNormalIn N)
  have hNleNormalizerE : N ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_of_isNormalIn hE_normal_N
  have hNormalizerE : Subgroup.normalizer (E : Set G) = M :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) hMmax
      (componentLayerOf_isNormalIn M).1 hEne
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := E)
        (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn M)))
  intro n hn
  exact hNormalizerE ▸ hNleNormalizerE hn

end CFSG.GorensteinWalter
