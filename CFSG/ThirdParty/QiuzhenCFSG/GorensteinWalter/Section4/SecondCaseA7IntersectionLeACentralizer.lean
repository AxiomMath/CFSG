module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreSylowIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddIndexCentralizesOrderThree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The even coset intersection centralizes the A7 order-nine subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- For a centralizing outside involution `y`, the intersection
`D = M ∩ M^y` lies in the centralizer in `M` of `A = K F`. -/
public theorem secondCase_a7_inter_conjugate_le_A_centralizer
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
    w.M ⊓ conjugateSubgroup w.M y ≤
      w.M ⊓ Subgroup.centralizer
        ((od.K ⊔ od.F : Subgroup G) : Set G) := by
  classical
  let D : Subgroup G := w.M ⊓ conjugateSubgroup w.M y
  let A : Subgroup G := od.K ⊔ od.F
  let V : Subgroup G := twoCoreOf c.Hhat
  have hAVleD : A ⊔ V ≤ D := by
    simpa [A, V, D] using
      secondCase_a7_A_sup_twoCore_le_inter_conjugate
        hmin c w d hA7 hmodel od hyH
  have hAleD : A ≤ D := le_sup_left.trans hAVleD
  have hVleD : V ≤ D := le_sup_right.trans hAVleD
  have hFleA : od.F ≤ A := le_sup_right
  have hFleD : od.F ≤ D := hFleA.trans hAleD
  have hFnormalD : IsNormalIn od.F D := by
    refine ⟨hFleD, ?_⟩
    intro x hx f hf
    exact od.F_normal_M.2 x hx.1 f hf
  have hAeq : A = c.U ⊓ w.M := by
    calc
      A = c.FU ⊓ w.M := by simpa [A] using od.FU_inter_M_eq
      _ = c.U ⊓ w.M := by
        rw [secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel]
  have hFleU : od.F ≤ c.U := hFleA.trans (hAeq.le.trans inf_le_left)
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    change twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G)
    rw [h26.1]
    exact twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVcentF : V ≤ Subgroup.centralizer (od.F : Set G) :=
    hVcentU.trans (Subgroup.centralizer_le hFleU)
  have hVindexNot : ¬ 2 ∣ (V.subgroupOf D).index := by
    simpa [V, D] using
      secondCase_a7_twoCore_subgroupOf_inter_index_odd
        hmin c w d hA7 hmodel od hy hyM hyH
  have hVindexOdd : Odd ((V.subgroupOf D).index) :=
    Nat.not_even_iff_odd.mp (fun hEven => hVindexNot (even_iff_two_dvd.mp hEven))
  have hDcentF : D ≤ Subgroup.centralizer (od.F : Set G) :=
    le_centralizer_of_card_three_normal_and_odd_centralizing_index
      D V od.F od.F_card hFnormalD hVleD hVcentF hVindexOdd
  have hFcentD : od.F ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.le_centralizer_iff.mp hDcentF
  let Z0 : Subgroup G := A ⊓ Subgroup.centralizer (D : Set G)
  have hFleZ0 : od.F ≤ Z0 := le_inf hFleA hFcentD
  have hZ0leA : Z0 ≤ A := inf_le_left
  have hAcard : Nat.card A = 9 := by
    rw [show A = od.K ⊔ od.F by rfl, od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hFdivZ0 : 3 ∣ Nat.card Z0 := by
    rw [← od.F_card]
    exact Subgroup.card_dvd_of_le hFleZ0
  have hZ0divA : Nat.card Z0 ∣ 9 := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le hZ0leA
  have hZ0card : Nat.card Z0 = 3 ∨ Nat.card Z0 = 9 := by
    obtain ⟨k, hk, hkcard⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card Z0 ∣ 3 ^ 2 by
        norm_num
        exact hZ0divA)
    interval_cases k
    · norm_num at hkcard
      norm_num [hkcard] at hFdivZ0
    · left
      simpa using hkcard
    · right
      simpa using hkcard
  have hZ0case : Z0 = od.F ∨ Z0 = A := by
    rcases hZ0card with h3 | h9
    · left
      exact (Subgroup.eq_of_le_of_card_ge hFleZ0 (by rw [h3, od.F_card])).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hZ0leA (by rw [h9, hAcard])
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyND : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D] using
      involution_mem_normalizer_inf_conjugateSubgroup w.M hy2
  have hAnormal : IsNormalIn A c.H := by
    simpa [A] using secondCase_a7_A_normal_H hmin c w d hA7 hmodel od
  have hyNA : y ∈ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_isNormalIn hAnormal hyH
  have hyNC : y ∈
      Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer_subgroup D hyND
  have hyNZ0 : y ∈ Subgroup.normalizer (Z0 : Set G) := by
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hyNA, hyNC⟩
  have hZ0eqA : Z0 = A := by
    rcases hZ0case with hZ0F | hZ0A
    · have hyNF : y ∈ Subgroup.normalizer (od.F : Set G) := by
        rw [← hZ0F]
        exact hyNZ0
      rw [od.F_normalizer] at hyNF
      exact False.elim (hyM hyNF)
    · exact hZ0A
  have hAcentD : A ≤ Subgroup.centralizer (D : Set G) := by
    rw [← hZ0eqA]
    exact inf_le_right
  have hDcentA : D ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff.mp hAcentD
  exact le_inf inf_le_left hDcentA

end CFSG.GorensteinWalter
