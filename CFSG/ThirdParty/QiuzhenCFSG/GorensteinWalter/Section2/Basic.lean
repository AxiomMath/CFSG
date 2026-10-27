module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample -- minimalCounterexample_isSimple and the centralizer setup witness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection -- reflection elements in the dihedral Sylow are involutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23IIHelpers -- inversion endpoint for Lemma 2.3(ii)
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28Helpers -- elementary normalizer and inverted-subgroup endpoints
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers -- elementary intersection endpoint for Lemma 2.9
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23II
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.HhatConjugateTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem210
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1 -- needed by the proofs of 2.7-2.9 (fact_1_4_*, fact_1_5_iii, centralizerIn, sqrtOf); make `public import` only if a Section2 statement cites a Section 1 name (Section3/Section4 do not import Section1)
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23ControlCore -- the control-core bridge: discharges `lemma_2_3` below (re-exports ControlCore)
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU -- lower acyclic proof of the recalled equality `H = S ⊔ O(H)`
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions -- local assembly from GW Lemma 2.1

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2: maximal subgroups related to an involution centralizer
-/

noncomputable section

open Matrix

namespace CFSG.GorensteinWalter

universe u

/-! ## Section 2 preamble facts (Bender p. 219) -/

/-- Section 2 preamble: all involutions of the minimal counterexample `G` are
conjugate ("We recall that all involutions of `G` are conjugate"). -/
public theorem fact_2_preamble_involutions_conjugate
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    ∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y := by
  exact fact_2_preamble_involutions_conjugate_proved hmin

/-- Section 2 preamble: `H = S·U`, i.e. `C_G(t) = S·O(C_G(t))` ("We recall
that ... `H` is `SU`").  The paper's product `SU` is the subgroup generated
by `S` and `U`, written here as the join. -/
public theorem fact_2_preamble_H_eq_SU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    (c.S : Subgroup G) ⊔ c.U = c.H := by
  exact fact_2_preamble_H_eq_SU_proved hmin c

/-- The equality alternative in Lemma 2.3(iii).  If the normalizer-control
arrows run both ways, the maximal subgroups coincide unless their generalized
Fitting subgroups are `p`-groups for one common prime.

Proof (via the control-core bridge of
`GorensteinWalter/Section2/ControlCore.lean`): the layer of `A` centralizes
`F(A)` (KS 6.5.2/6.5.3, proved in `ControlCore.lean`), so
`NormalizerControlledBy` yields the `ControlCore` relation
(`controlCore_of_normalizerControlledBy`), and the arrow form
`lemma_2_3_of_controlCore` (Bender [1, 1.6/1.7]) gives the alternative. -/
public theorem lemma_2_3
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    {A M : Subgroup G}
    (hA : IsCoatom A) (hM : IsCoatom M)
    (hAM : NormalizerControlledBy A M)
    (hMA : NormalizerControlledBy M A) :
    A = M ∨
      ∃ p : ℕ, p.Prime ∧
        IsPGroup p (generalizedFittingSubgroupOf A) ∧
          IsPGroup p (generalizedFittingSubgroupOf M) :=
  lemma_2_3_of_controlCore (minimalCounterexample_isSimple hmin) hA hM
    (controlCore_of_normalizerControlledBy hAM)
    (controlCore_of_normalizerControlledBy hMA)

end CFSG.GorensteinWalter
