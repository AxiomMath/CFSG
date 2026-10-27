module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAlignedA
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAlignedConjugator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearCenterless
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenCentralizerChain
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPNotConjP0
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The concrete aligned equation-(11) centralizer chain

This owner packages the aligned representative, stabilization of `A`, and
the exact `C_E(P₀)` normalizer/centralizer identities for every outer-region
conjugate `X`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every conjugate `X ≠ P` lying in `A` admits an aligned representative
and satisfies the exact first equation-(11) identity chain. -/
public theorem secondCase_linear_aligned_chain
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (post : SecondCaseLinearPostNineData c w d K)
    (X : Subgroup G)
    (hXleA : X ≤ post.od.A) (hXneP : X ≠ post.od.P)
    (hXconj : ∃ g : G, X = conjugateSubgroup post.od.P g) :
    ∃ g : G,
      X = conjugateSubgroup post.od.P g ∧
      g * c.t * g⁻¹ = c.t ∧
      conjugateSubgroup post.od.A g = post.od.A ∧
      (conjugateSubgroup w.M g ⊓ (post.od.P ⊔ d.E) =
          (post.od.P ⊔ d.E) ⊓ Subgroup.normalizer (X : Set G)) ∧
      ((post.od.P ⊔ d.E) ⊓ Subgroup.normalizer (X : Set G) =
          post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E)) ∧
      (post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) =
          (post.od.P ⊔ d.E) ⊓ Subgroup.centralizer (post.od.A : Set G)) ∧
      (d.E ⊓ Subgroup.normalizer (X : Set G) =
          Subgroup.centralizer (post.od.P0 : Set G) ⊓ d.E) := by
  have hPnot : ¬ ∃ z : G,
      conjugateSubgroup post.od.P z = post.od.P0 :=
    secondCase_linear_P_not_conjugate_P0 c w d K post
  obtain ⟨g, hgX, hfix⟩ :=
    secondCase_linear_aligned_exists_conjugator_fixing_t c w d K post X hXleA hXconj
  have hXeq : X = conjugateSubgroup post.od.P g := hgX.symm
  have hAg : conjugateSubgroup post.od.A g = post.od.A :=
    secondCase_linear_aligned_A_conjugate_eq_A
      hmin c w d K hK e post hPnot hXleA hXneP hXeq hfix
  have hZ : Subgroup.center d.E = ⊥ :=
    secondCase_linear_center_eq_bot hmin c w d K hK e post
  have hchain :=
    secondCase_linearEquation11_first_identity_chain_of_P0_centralizer
      hmin c w d K hK e post hZ g hXeq hXleA hXneP hAg hPnot
  exact ⟨g, hXeq, hfix, hAg, hchain⟩

end CFSG.GorensteinWalter
