module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaDataOfAlignedSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearK0NormalAligned

namespace CFSG
end CFSG
open CFSG

/-!
# Unconditional aligned `K₀` normality

The aligned omega-data producer now proves source equation (1).  This small
wrapper feeds that equality directly to the aligned `K₀` normality endpoint,
leaving the latter theorem available as a source-facing conditional lemma as
well.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_linear_K0_normal_H_inter_M_of_alignedSylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E) :
    ∃ od : SecondCaseLinearOmegaData c w d,
      od.s ∈ (SE : Subgroup d.E) ∧
        IsNormalIn od.K0 (c.H ⊓ w.M) := by
  obtain ⟨od, hsSE, _hsS, _hsS0, _hF_eq, _hBcentSE, _hKnormSE,
      hKcomm⟩ :=
    secondCase_linear_omegaData_of_alignedSylow
      hmin c w d K hK e SM hSMleS SE hSEamb
  refine ⟨od, hsSE, ?_⟩
  exact secondCase_linear_K0_normal_H_inter_M_of_aligned_commutator
    hmin c w d K hK e SM hSMcent hSMleS SE hSEamb od hsSE hKcomm

end CFSG.GorensteinWalter
