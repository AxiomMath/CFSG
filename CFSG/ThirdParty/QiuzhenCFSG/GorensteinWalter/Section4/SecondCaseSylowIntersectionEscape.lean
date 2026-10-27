module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SylowIntersectionNormalizerGrowth
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

namespace CFSG
end CFSG
open CFSG

/-!
# The first ambient-Sylow escape step in Section 4

This formalizes the source implication

`not (S ≤ E) ⇒ not (S ∩ M ≤ E)`

from the equation-(5) identification
`F = C_{F(U)}(S ∩ E)` and `N_G(F) = M`.  The remaining PSL₂ argument
starts by choosing an involution in `S ∩ M \ E`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `F = C_{F(U)}(S ∩ E)` has normalizer `M`, then failure of
`S ≤ E` produces an element of `S ∩ M` outside `E`.

Indeed, `S` normalizes `F(U)`, and `N_S(S ∩ E)` normalizes the
centralizer of `S ∩ E`; hence it normalizes `F` and lies in `M`.  The
normalizer condition inside the Sylow `2`-group then gives the escape
element. -/
public theorem secondCase_sylow_intersection_not_le_component_of_fitting_centralizer
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (F : Subgroup G)
    (hF_eq : F = c.FU ⊓
      Subgroup.centralizer
        ((((c.S : Subgroup G) ⊓ d.E) : Subgroup G) : Set G))
    (hNF : Subgroup.normalizer (F : Set G) = w.M)
    (hSnotE : ¬ (c.S : Subgroup G) ≤ d.E) :
    ¬ ((c.S : Subgroup G) ⊓ w.M) ≤ d.E := by
  have hSleNFU : (c.S : Subgroup G) ≤
      Subgroup.normalizer (c.FU : Set G) :=
    (centralizerSetup_S_le_H c).trans
      (le_normalizer_of_isNormalIn (centralizerSetup_FU_isNormalIn_H c))
  have hinner : (c.S : Subgroup G) ⊓
      Subgroup.normalizer
        ((((c.S : Subgroup G) ⊓ d.E) : Subgroup G) : Set G) ≤ w.M := by
    intro x hx
    have hxNC : x ∈ Subgroup.normalizer
        (Subgroup.centralizer
          ((((c.S : Subgroup G) ⊓ d.E) : Subgroup G) : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer_subgroup
        (((c.S : Subgroup G) ⊓ d.E) : Subgroup G) hx.2
    have hxNF : x ∈ Subgroup.normalizer
        ((c.FU ⊓ Subgroup.centralizer
          ((((c.S : Subgroup G) ⊓ d.E) : Subgroup G) : Set G)) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hSleNFU hx.1, hxNC⟩
    have hxNF' : x ∈ Subgroup.normalizer (F : Set G) := by
      rw [hF_eq]
      exact hxNF
    rw [hNF] at hxNF'
    exact hxNF'
  exact sylow_intersection_not_le_of_inner_normalizer_le
    c.S d.E w.M hSnotE hinner

end CFSG.GorensteinWalter
