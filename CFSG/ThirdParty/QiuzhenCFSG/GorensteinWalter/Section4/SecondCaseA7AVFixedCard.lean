module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreFixedCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ANormalH
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreCentralizerEqualsHhat
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Fixed points on the A7 order-thirty-six subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A centralizing outside involution has six fixed points on
`A V = (K F) O2(Hhat)`. -/
public theorem secondCase_a7_A_sup_twoCore_fixed_card_eq_six
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
    Nat.card (centralizerIn
      ((od.K ⊔ od.F) ⊔ twoCoreOf c.Hhat) y) = 6 := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let V : Subgroup G := twoCoreOf c.Hhat
  let AV : Subgroup G := A ⊔ V
  let CA : Subgroup G := centralizerIn A y
  let CV : Subgroup G := centralizerIn V y
  let CAV : Subgroup G := centralizerIn AV y
  have hAnormal : IsNormalIn A c.H := by
    simpa [A] using secondCase_a7_A_normal_H hmin c w d hA7 hmodel od
  have hAleH : A ≤ c.H := hAnormal.1
  have hVeqH : twoCoreOf c.H = V := by
    simpa [V] using
      twoCoreOf_H_eq_twoCoreOf_Hhat_of_centralizerStructure c
        (theorem_2_6 hmin c)
  have hVnormal : IsNormalIn V c.H := by
    rw [← hVeqH]
    exact twoCoreOf_isNormalIn c.H
  have hVleH : V ≤ c.H := hVnormal.1
  have hAVleH : AV ≤ c.H := sup_le hAleH hVleH
  have hAVleD : AV ≤ w.M ⊓ conjugateSubgroup w.M y := by
    simpa [AV, A, V] using
      secondCase_a7_A_sup_twoCore_le_inter_conjugate
        hmin c w d hA7 hmodel od hyH
  have hDcentA : w.M ⊓ conjugateSubgroup w.M y ≤
      Subgroup.centralizer (A : Set G) := by
    have h := secondCase_a7_inter_conjugate_le_A_centralizer
      hmin c w d hA7 hmodel od hy hyM hyH
    exact (by simpa [A] using h.trans inf_le_right)
  have hVcentA : V ≤ Subgroup.centralizer (A : Set G) :=
    le_sup_right.trans hAVleD |>.trans hDcentA
  have hAcard : Nat.card A = 9 := by
    rw [show A = od.K ⊔ od.F by rfl, od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hVcard : Nat.card V = 4 := by
    have hVKint := (secondCase_a7_klein_branch hmin c w d hA7 hmodel).1
    have hVK : IsKleinFour V := by
      change IsKleinFour ((pCore 2 c.Hhat).map c.Hhat.subtype)
      exact isKleinFour_map_of_injective
        (pCore 2 c.Hhat) hVKint c.Hhat.subtype c.Hhat.subtype_injective
    exact hVK.card_four
  have hAVdisj : Disjoint A V := by
    rw [disjoint_iff]
    let I : Subgroup G := A ⊓ V
    have hIdvdA : Nat.card I ∣ 9 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hIdvdV : Nat.card I ∣ 4 := by
      rw [← hVcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hIcard : Nat.card I = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num) hIdvdA hIdvdV
    change I = ⊥
    exact (Subgroup.eq_bot_iff_card (H := I)).mpr hIcard
  have hfixedEq : CAV = CA ⊔ CV := by
    apply le_antisymm
    · intro x hx
      let xH : c.H := ⟨x, hAVleH hx.1⟩
      let AH : Subgroup c.H := A.subgroupOf c.H
      let VH : Subgroup c.H := V.subgroupOf c.H
      have hsubEq : AV.subgroupOf c.H = AH ⊔ VH := by
        simpa [AV, AH, VH] using Subgroup.subgroupOf_sup hAleH hVleH
      have hxSup : xH ∈ AH ⊔ VH := by
        rw [← hsubEq]
        exact hx.1
      let : AH.Normal :=
        (Subgroup.normal_subgroupOf_iff hAleH).2
          (fun a h haA hh => hAnormal.2 h hh a haA)
      rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
        ⟨aH, haAH, vH, hvVH, havx⟩
      let a : G := aH
      let v : G := vH
      have haA : a ∈ A := haAH
      have hvV : v ∈ V := hvVH
      have havxG : a * v = x := congrArg Subtype.val havx
      let ay : G := y * a * y⁻¹
      let vy : G := y * v * y⁻¹
      have hayA : ay ∈ A := hAnormal.2 y hyH a haA
      have hvyV : vy ∈ V := hVnormal.2 y hyH v hvV
      have hxfix : y * x * y⁻¹ = x := by
        have hcomm :=
          (Subgroup.mem_centralizer_iff.mp hx.2) y (by simp)
        rw [hcomm]
        group
      have hprodEq : ay * vy = a * v := by
        calc
          ay * vy = y * (a * v) * y⁻¹ := by
            dsimp [ay, vy]
            group
          _ = y * x * y⁻¹ := by rw [havxG]
          _ = x := hxfix
          _ = a * v := havxG.symm
      have hdiscEq : a⁻¹ * ay = v * vy⁻¹ := by
        calc
          a⁻¹ * ay = a⁻¹ * (ay * vy) * vy⁻¹ := by group
          _ = a⁻¹ * (a * v) * vy⁻¹ := by rw [hprodEq]
          _ = v * vy⁻¹ := by group
      have hdiscA : a⁻¹ * ay ∈ A := A.mul_mem (A.inv_mem haA) hayA
      have hdiscV : a⁻¹ * ay ∈ V := by
        rw [hdiscEq]
        exact V.mul_mem hvV (V.inv_mem hvyV)
      have hdiscOne : a⁻¹ * ay = 1 :=
        (Subgroup.disjoint_def.mp hAVdisj) hdiscA hdiscV
      have hay : ay = a := by
        calc
          ay = a * (a⁻¹ * ay) := by group
          _ = a := by rw [hdiscOne]; simp
      have hvprod : v * vy⁻¹ = 1 := hdiscEq.symm.trans hdiscOne
      have hvy : vy = v := (mul_inv_eq_one.mp hvprod).symm
      have haCA : a ∈ CA := by
        refine ⟨haA, ?_⟩
        have hmul := congrArg (fun q : G => q * y) hay
        have hcomm : y * a = a * y := by simpa [ay, mul_assoc] using hmul
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
      have hvCV : v ∈ CV := by
        refine ⟨hvV, ?_⟩
        have hmul := congrArg (fun q : G => q * y) hvy
        have hcomm : y * v = v * y := by simpa [vy, mul_assoc] using hmul
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
      rw [← havxG]
      exact Subgroup.mul_mem_sup haCA hvCV
    · exact sup_le
        (fun _ hx => ⟨(le_sup_left : A ≤ AV) hx.1, hx.2⟩)
        (fun _ hx => ⟨(le_sup_right : V ≤ AV) hx.1, hx.2⟩)
  have hCAcard : Nat.card CA = 3 := by
    simpa [CA, A] using
      secondCase_a7_A_fixed_card_eq_three hmin c w d hA7 hmodel od hy hyM hyH
  have hCVcard : Nat.card CV = 2 := by
    simpa [CV, V] using
      secondCase_a7_twoCore_fixed_card_eq_two
        hmin c w d hA7 hmodel od hy hyM hyH
  have hCAdisjCV : Disjoint CA CV := by
    exact hAVdisj.mono inf_le_left inf_le_left
  have hCVcentCA : CV ≤ Subgroup.centralizer (CA : Set G) :=
    inf_le_left.trans (hVcentA.trans (Subgroup.centralizer_le inf_le_left))
  have hCVnormCA : CV ≤ Subgroup.normalizer (CA : Set G) :=
    hCVcentCA.trans (Subgroup.centralizer_le_normalizer (CA : Set G))
  have hjoinCard : Nat.card (CA ⊔ CV : Subgroup G) = 6 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer
      CA CV hCVnormCA hCAdisjCV, hCAcard, hCVcard]
  rw [show centralizerIn ((od.K ⊔ od.F) ⊔ twoCoreOf c.Hhat) y = CAV by rfl,
    hfixedEq]
  exact hjoinCard

end CFSG.GorensteinWalter
