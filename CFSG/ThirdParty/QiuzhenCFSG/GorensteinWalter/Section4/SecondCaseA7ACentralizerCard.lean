module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OddCoreEqF
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KleinFourLeTwoCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreEquality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardExactUnconditional
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeSubgroupCentralizerCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourQuotientOddKernel
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerMap
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptionTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The centralizer bound used in the A7 even-coset count -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 case, the centralizer in `M` of the equation-(8) subgroup
`A = K F` has order at most `108`. -/
public theorem secondCase_a7_A_centralizer_card_le_108
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    Nat.card (w.M ⊓ Subgroup.centralizer
      ((od.K ⊔ od.F : Subgroup G) : Set G) : Subgroup G) ≤ 108 := by
  classical
  let M : Subgroup G := w.M
  let A : Subgroup G := od.K ⊔ od.F
  let C : Subgroup G := M ⊓ Subgroup.centralizer (A : Set G)
  let O : Subgroup M := pPrimeCore 2 M
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  have hAeq : A = c.U ⊓ M := by
    calc
      A = c.FU ⊓ M := by simpa [A, M] using od.FU_inter_M_eq
      _ = c.U ⊓ M := by
        rw [secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel]
  have hAleM : A ≤ M := hAeq.le.trans inf_le_right
  have hAleU : A ≤ c.U := hAeq.le.trans inf_le_left
  let AM : Subgroup M := A.subgroupOf M
  let Abar : Subgroup (M ⧸ O) := AM.map q
  let eQ : (M ⧸ O) ≃* alternatingGroup (Fin 7) :=
    (secondCase_a7_ambient_quotient_model hmin c w d hA7 hmodel).some
  let A7sub : Subgroup (alternatingGroup (Fin 7)) :=
    Abar.map eQ.toMonoidHom
  have hAMeq : AM = (c.U ⊓ M).subgroupOf M := by
    dsimp [AM]
    rw [hAeq]
  have hAbarCard : Nat.card Abar = 3 := by
    rw [show Abar = AM.map q by rfl, hAMeq]
    simpa [M, O, q] using
      secondCase_a7_u_inter_m_quotient_card_eq_three hmin c w d hA7 hmodel
  have hA7card : Nat.card A7sub = 3 := by
    rw [show A7sub = Abar.map eQ.toMonoidHom by rfl,
      Subgroup.card_map_of_injective eQ.injective, hAbarCard]
  obtain ⟨V, hVK, hVleCore⟩ :=
    secondCase_a7_exists_kleinFour_le_twoCore_Hhat hmin c w d hA7 hmodel
  have hCoreEq :=
    secondCase_a7_twoCore_inter_eq_twoCore_Hhat hmin c w d hA7 hmodel
  have hVleHM : V ≤ c.H ⊓ M := by
    rw [← hCoreEq] at hVleCore
    exact hVleCore.trans
      (Subgroup.map_subtype_le (pCore 2 (c.H ⊓ M : Subgroup G)))
  have hVleM : V ≤ M := hVleHM.trans inf_le_right
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    apply hVleCore.trans
    rw [h26.1]
    exact twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hVcentA : V ≤ Subgroup.centralizer (A : Set G) :=
    hVcentU.trans (Subgroup.centralizer_le hAleU)
  let VM : Subgroup M := V.subgroupOf M
  have hVMK : IsKleinFour VM := isKleinFour_subgroupOf hVleM hVK
  have hVMcentAM : VM ≤ Subgroup.centralizer (AM : Set M) := by
    simpa [VM, AM] using centralizer_subgroupOf_le hAleM hVleM hVcentA
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := M))
  let Vbar : Subgroup (M ⧸ O) := VM.map q
  have hVbarK : IsKleinFour Vbar := by
    simpa [Vbar, q] using
      isKleinFour_map_quotient_of_odd_kernel O VM hOodd hVMK
  have hVbarcent : Vbar ≤
      Subgroup.centralizer (Abar : Set (M ⧸ O)) := by
    simpa [Vbar, Abar] using
      centralizer_map_le_of_hom q AM VM hVMcentAM
  let V7 : Subgroup (alternatingGroup (Fin 7)) :=
    Vbar.map eQ.toMonoidHom
  have hV7K : IsKleinFour V7 := by
    simpa [V7] using isKleinFour_map_mulEquiv_cross Vbar hVbarK eQ
  have hV7cent : V7 ≤ Subgroup.centralizer
      (A7sub : Set (alternatingGroup (Fin 7))) := by
    simpa [V7, A7sub] using
      centralizer_map_le_of_mulEquiv eQ Abar Vbar hVbarcent
  have hCentA7card : Nat.card (Subgroup.centralizer
      (A7sub : Set (alternatingGroup (Fin 7)))) = 36 :=
    aSeven_order_three_subgroup_centralizer_card_eq_thirty_six
      A7sub V7 hA7card hV7K hV7cent
  let C0 : Subgroup M := C.subgroupOf M
  let Cbar : Subgroup (M ⧸ O) := C0.map q
  let C7 : Subgroup (alternatingGroup (Fin 7)) := Cbar.map eQ.toMonoidHom
  have hCleM : C ≤ M := inf_le_left
  have hCleCent : C ≤ Subgroup.centralizer (A : Set G) := inf_le_right
  have hC0cent : C0 ≤ Subgroup.centralizer (AM : Set M) := by
    simpa [C0, AM] using centralizer_subgroupOf_le hAleM hCleM hCleCent
  have hCbarcent : Cbar ≤
      Subgroup.centralizer (Abar : Set (M ⧸ O)) := by
    simpa [Cbar, Abar] using centralizer_map_le_of_hom q AM C0 hC0cent
  have hC7cent : C7 ≤ Subgroup.centralizer
      (A7sub : Set (alternatingGroup (Fin 7))) := by
    simpa [C7, A7sub] using
      centralizer_map_le_of_mulEquiv eQ Abar Cbar hCbarcent
  have hC7le : Nat.card C7 ≤ 36 := by
    rw [← hCentA7card]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hC7cent)
  have hCbarCard : Nat.card Cbar = Nat.card C7 :=
    (Subgroup.card_map_of_injective eQ.injective).symm
  have hCbarLe : Nat.card Cbar ≤ 36 := by
    rw [hCbarCard]
    exact hC7le
  have hOcard : Nat.card O = 3 := by
    have hmapCard : Nat.card (O.map M.subtype) = Nat.card O :=
      Subgroup.card_map_of_injective M.subtype_injective
    have hmapEq : O.map M.subtype = od.F := by
      simpa [M, O, oddCoreOf] using
        secondCase_a7_oddCore_eq_F hmin c w d hA7 hmodel od
    rw [← hmapCard, hmapEq, od.F_card]
  have hker : q.ker = O := QuotientGroup.ker_mk' O
  have hkerLe : Nat.card (C0 ⊓ q.ker : Subgroup M) ≤ 3 := by
    have hdiv : Nat.card (C0 ⊓ q.ker : Subgroup M) ∣ Nat.card O := by
      rw [hker]
      exact Subgroup.card_dvd_of_le inf_le_right
    rw [hOcard] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hC0card := card_map_eq_card_mul_card_ker q C0
  have hC0le : Nat.card C0 ≤ 108 := by
    rw [hC0card]
    calc
      Nat.card Cbar * Nat.card (C0 ⊓ q.ker : Subgroup M) ≤ 36 * 3 :=
        Nat.mul_le_mul hCbarLe hkerLe
      _ = 108 := by norm_num
  have hCcard : Nat.card C = Nat.card C0 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv).symm
  simpa [M, A, C] using hCcard.trans_le hC0le

end CFSG.GorensteinWalter
