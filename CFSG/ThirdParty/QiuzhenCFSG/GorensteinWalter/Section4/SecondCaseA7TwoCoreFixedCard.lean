module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AFixedCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreSylowIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizedKleinFourInvolutionDihedral
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseEvenNormalizedInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreCentralizerEqualsHhat
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Fixed points on the A7 Klein four -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A centralizing outside involution has exactly two fixed points on
`V = O2(Hhat)`. -/
public theorem secondCase_a7_twoCore_fixed_card_eq_two
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
    Nat.card (centralizerIn (twoCoreOf c.Hhat) y) = 2 := by
  classical
  let V : Subgroup G := twoCoreOf c.Hhat
  let Z : Subgroup G := Subgroup.zpowers y
  let P : Subgroup G := V ⊔ Z
  let C : Subgroup G := centralizerIn V y
  have hVKint : IsKleinFour (pCore 2 c.Hhat) :=
    (secondCase_a7_klein_branch hmin c w d hA7 hmodel).1
  have hVK : IsKleinFour V := by
    change IsKleinFour ((pCore 2 c.Hhat).map c.Hhat.subtype)
    exact isKleinFour_map_of_injective
      (pCore 2 c.Hhat) hVKint c.Hhat.subtype c.Hhat.subtype_injective
  have hVeqH : twoCoreOf c.H = V := by
    simpa [V] using
      twoCoreOf_H_eq_twoCoreOf_Hhat_of_centralizerStructure c
        (theorem_2_6 hmin c)
  have hVnormal : IsNormalIn V c.H := by
    rw [← hVeqH]
    exact twoCoreOf_isNormalIn c.H
  have hyNV : y ∈ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_isNormalIn hVnormal hyH
  have hVleD : V ≤ w.M ⊓ conjugateSubgroup w.M y := by
    exact le_sup_right.trans
      (secondCase_a7_A_sup_twoCore_le_inter_conjugate
        hmin c w d hA7 hmodel od hyH)
  have hyV : y ∉ V := fun hyV => hyM (hVleD hyV).1
  have hScard : Nat.card (c.S : Subgroup G) = 8 :=
    secondCase_a7_S_card_eq_eight hmin c w d hA7 hmodel
  let eP : P ≃* DihedralGroup 4 :=
    (normalized_kleinFour_sup_involution_is_dihedral_four
      c.S hScard c.dihedralEquiv.some V hVK hy hyV hyNV).some
  have hCnontrivial : Nat.card C ≠ 1 := by
    obtain ⟨s, hsI, hsV, hsy⟩ :=
      exists_centralizing_involution_of_even_normalized V hy hyNV (by
        rw [hVK.card_four]
        norm_num)
    have hsC : s ∈ C := by
      refine ⟨hsV, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hsy
    intro hcard
    have hCbot : C = ⊥ := (Subgroup.eq_bot_iff_card (H := C)).mpr hcard
    have hsbot : s ∈ (⊥ : Subgroup G) := by rw [← hCbot]; exact hsC
    exact hsI.1 (Subgroup.mem_bot.mp hsbot)
  have hCneV : C ≠ V := by
    intro hCV
    have hVcentV : V ≤ Subgroup.centralizer (V : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hcomm := hVK.isMulCommutative.is_comm.comm
        (⟨v, hv⟩ : V) (⟨u, hu⟩ : V)
      exact (congrArg Subtype.val hcomm).symm
    have hVcentZ : V ≤ Subgroup.centralizer (Z : Set G) := by
      intro v hv
      change v ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hvC : v ∈ C := by rw [hCV]; exact hv
      exact hvC.2
    have hZcentV : Z ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.le_centralizer_iff.mp hVcentZ
    have hZcentZ : Z ≤ Subgroup.centralizer (Z : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      let : IsCyclic Z := Subgroup.isCyclic_zpowers y
      have hcomm := (inferInstance : IsMulCommutative Z).is_comm.comm
        (⟨z, hz⟩ : Z) (⟨u, hu⟩ : Z)
      exact (congrArg Subtype.val hcomm).symm
    have hVcentP : V ≤ Subgroup.centralizer (P : Set G) := by
      exact le_centralizer_sup_of_le_centralizers hVcentV hVcentZ
    have hZcentP : Z ≤ Subgroup.centralizer (P : Set G) := by
      exact le_centralizer_sup_of_le_centralizers hZcentV hZcentZ
    have hPcent : P ≤ Subgroup.centralizer (P : Set G) :=
      sup_le hVcentP hZcentP
    have hPcomm : IsMulCommutative P := by
      refine ⟨⟨?_⟩⟩
      intro a b
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp (hPcent a.2)) (b : G) b.2
      exact Subtype.ext hcomm.symm
    have hmodel : IsMulCommutative (DihedralGroup 4) := by
      refine ⟨⟨?_⟩⟩
      intro a b
      have hab := hPcomm.is_comm.comm (eP.symm a) (eP.symm b)
      apply eP.symm.injective
      simpa using hab
    exact (DihedralGroup.not_commutative (by norm_num) (by norm_num)) hmodel
  have hCleV : C ≤ V := inf_le_left
  have hCdiv : Nat.card C ∣ 4 := by
    rw [← hVK.card_four]
    exact Subgroup.card_dvd_of_le hCleV
  have hCneFour : Nat.card C ≠ 4 := by
    intro hcard
    apply hCneV
    exact Subgroup.eq_of_le_of_card_ge hCleV (by rw [hcard, hVK.card_four])
  obtain ⟨k, hk, hCcard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card C ∣ 2 ^ 2 by
      norm_num
      exact hCdiv)
  interval_cases k
  · exact False.elim
      (hCnontrivial (by simpa only [pow_zero] using hCcard))
  · simpa only [pow_one] using hCcard
  · apply False.elim
    apply hCneFour
    norm_num only [pow_succ, pow_zero, mul_one] at hCcard ⊢
    exact hCcard

end CFSG.GorensteinWalter
