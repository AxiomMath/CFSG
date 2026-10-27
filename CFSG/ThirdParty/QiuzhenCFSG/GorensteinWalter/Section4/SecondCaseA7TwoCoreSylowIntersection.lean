module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AVLeIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SylowCardEight
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSylowOfNormalizedInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreCentralizerEqualsHhat
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreNormal

namespace CFSG
end CFSG
open CFSG

/-! # The Klein four is Sylow in the even coset intersection -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- For a centralizing outside involution `y`, the equation-(7) Klein four
`O2(Hhat)` has odd index in `D = M ∩ M^y`, and hence is Sylow there. -/
public theorem secondCase_a7_twoCore_subgroupOf_inter_index_odd
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ w.M) (hyH : y ∈ c.H) :
    ¬ 2 ∣ ((twoCoreOf c.Hhat).subgroupOf
      (w.M ⊓ conjugateSubgroup w.M y)).index := by
  let D : Subgroup G := w.M ⊓ conjugateSubgroup w.M y
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVleD : V ≤ D := by
    exact le_sup_right.trans
      (secondCase_a7_A_sup_twoCore_le_inter_conjugate
        hmin c w d hA7 hmodel od hyH)
  have hVKint : IsKleinFour (pCore 2 c.Hhat) :=
    (secondCase_a7_klein_branch hmin c w d hA7 hmodel).1
  have hVK : IsKleinFour V := by
    change IsKleinFour ((pCore 2 c.Hhat).map c.Hhat.subtype)
    exact isKleinFour_map_of_injective
      (pCore 2 c.Hhat) hVKint c.Hhat.subtype c.Hhat.subtype_injective
  have hyD : y ∉ D := fun hyD => hyM hyD.1
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyND : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D] using
      involution_mem_normalizer_inf_conjugateSubgroup w.M hy2
  have hVeqH : twoCoreOf c.H = V := by
    simpa [V] using
      twoCoreOf_H_eq_twoCoreOf_Hhat_of_centralizerStructure c
        (theorem_2_6 hmin c)
  have hVnormal : IsNormalIn V c.H := by
    rw [← hVeqH]
    exact twoCoreOf_isNormalIn c.H
  have hyNV : y ∈ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_isNormalIn hVnormal hyH
  have hScard : Nat.card (c.S : Subgroup G) = 8 :=
    secondCase_a7_S_card_eq_eight hmin c w d hA7 hmodel
  simpa [D, V] using
    kleinFour_subgroupOf_has_odd_index_of_normalized_outside_involution
      c.S hScard D V hVleD hVK hy hyD hyND hyNV

end CFSG.GorensteinWalter
