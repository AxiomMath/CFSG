module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearNoNormalInvertedException
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNilpotentNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The equation-(8) normalizer-index bound after equation (9)
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Once `S0` centralizes `U`, every branch of the omega trichotomy gives
`|U : N_U(A)| ≤ p`.  In the inversion branch, Lemma 2.8 excludes the normal
inverted-set exception. -/
public theorem secondCase_linear_omega_normalizerIndex_le_p
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hsS : (od.s : G) ∈ (c.S : Subgroup G))
    (hsS0 : (od.s : G) ∉ c.S0)
    (hS0centU : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (c.U : Set G)) :
    (normalizerIn c.U od.A).relIndex c.U ≤ od.p := by
  rcases secondCase_linear_omega_trichotomy c w d od with
    heq | hstrict | hinv
  · have heqData := secondCase_linear_omega_equality_index c w d od heq
    rw [heqData.2.1]
    exact od.hp_prime.one_le
  · exact secondCase_linear_omega_strict_normalizerIndex_le_p
      c w d od hstrict
  · have hF_full : od.F = centralizerIn c.FU (od.s : G) := by
      have hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
        c.U c.FU w.M od.F od.B (od.s : G)
        (fittingSubgroupOf_isNilpotent c.U)
        (fittingSubgroupOf_isNormalIn c.U)
        od.F_fixed od.B_fixed od.F_normalizer
      exact hfull.1
    have hno : ¬ (∃ I : Subgroup G,
        (I : Set G) = invertedElements c.U (od.s : G) ∧
          IsNormalIn I c.Hhat) :=
      secondCase_linear_no_normal_inverted_exception
        hmin c hS0centU (od.s : G) hsS hsS0
    exact (secondCase_linear_omega_inversion_endpoint
      hmin c w d od hF_full hinv).2 hno |>.1

end CFSG.GorensteinWalter
