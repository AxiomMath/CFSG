module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaTrichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaEqualityIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaStrictIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaInversionEndpoint
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNilpotentNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal

namespace CFSG
end CFSG
open CFSG

/-!
# The unconditional equation-(8) relative-index bound

The three alternatives of the linear omega trichotomy all give the same
relative-index conclusion.  The inversion branch first upgrades the
restricted fixed subgroup to the full centralizer in `F(U)` and then applies
its endpoint theorem.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Equation (8)'s relative-index bound, assembled from the linear omega
trichotomy. -/
public theorem secondCase_linear_equationEight_relIndex_le_p
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p := by
  rcases secondCase_linear_omega_trichotomy c w d od with
    heq | hstrict | hinv
  · exact (secondCase_linear_omega_equality_index c w d od heq).2.2
  · exact secondCase_linear_omega_strict_relIndex_le_p c w d od hstrict
  · have hF_full : od.F = centralizerIn c.FU (od.s : G) := by
      have hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
        c.U c.FU w.M od.F od.B (od.s : G)
        (fittingSubgroupOf_isNilpotent c.U)
        (fittingSubgroupOf_isNormalIn c.U)
        od.F_fixed od.B_fixed od.F_normalizer
      exact hfull.1
    exact (secondCase_linear_omega_inversion_endpoint
      hmin c w d od hF_full hinv).1

end CFSG.GorensteinWalter
