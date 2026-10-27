module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UNotLeM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FixedSubgroupsEq
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The center of the A7 odd core -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- For the synchronized A7 data, the inverted order-three subgroup `K` is
the ambient image of `Z(U)`. -/
public theorem secondCase_a7_K_eq_center_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    od.K = (Subgroup.center c.U).map c.U.subtype := by
  classical
  let Z : Subgroup G := (Subgroup.center c.U).map c.U.subtype
  have hZeq : Z = centerIn c.U := by
    dsimp [Z]
    ext x
    simp [centerIn, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff,
      and_comm]
  have hFleU : od.F ≤ c.U := by
    rw [← secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel]
    exact le_sup_right.trans (od.FU_inter_M_eq.le.trans inf_le_left)
  have hZleU : Z ≤ c.U := by rw [hZeq]; exact inf_le_left
  have hZcentU : Z ≤ Subgroup.centralizer (c.U : Set G) := by
    rw [hZeq]
    exact inf_le_right
  have hZcentF : Z ≤ Subgroup.centralizer (od.F : Set G) :=
    hZcentU.trans (Subgroup.centralizer_le (SetLike.coe_mono hFleU))
  have hZleM : Z ≤ w.M := by
    rw [← od.F_normalizer]
    exact hZcentF.trans (Subgroup.centralizer_le_normalizer (od.F : Set G))
  have hZnormalH : IsNormalIn Z c.H := by
    dsimp [Z]
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := Subgroup.center c.U) (hKchar := Subgroup.centerCharacteristic)
      (centralizerSetup_U_isNormalIn_H c)
  have hsZ : ∀ x : G, x ∈ Z → (od.s : G) * x * (od.s : G)⁻¹ ∈ Z := by
    intro x hx
    exact hZnormalH.2 (od.s : G) od.s_mem_H x hx
  have hZodd : Odd (Nat.card Z) := by
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hZleU)
  have hCZbot : centralizerIn Z (od.s : G) = ⊥ := by
    by_contra hCne
    let C : Subgroup G := centralizerIn Z (od.s : G)
    have hCleF : C ≤ od.F := by
      intro x hx
      have hxU : x ∈ c.U := hZleU hx.1
      have hxB : x ∈ od.B := by
        rw [od.B_fixed, centralizerIn]
        exact ⟨hxU, hx.2⟩
      rw [secondCase_a7_fixed_subgroups_eq hmin c w d hA7 hmodel od] at hxB
      exact hxB
    have hCcardDvd : Nat.card C ∣ 3 := by
      rw [← od.F_card]
      exact Subgroup.card_dvd_of_le hCleF
    have hCcard : Nat.card C = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hCcardDvd with h1 | h3
      · exact False.elim (hCne ((Subgroup.eq_bot_iff_card (H := C)).mpr h1))
      · exact h3
    have hCeqF : C = od.F :=
      Subgroup.eq_of_le_of_card_ge hCleF (by rw [hCcard, od.F_card])
    have hFleZ : od.F ≤ Z := by
      rw [← hCeqF]
      exact inf_le_left
    have hFcentU : od.F ≤ Subgroup.centralizer (c.U : Set G) :=
      hFleZ.trans hZcentU
    have hUcentF : c.U ≤ Subgroup.centralizer (od.F : Set G) :=
      Subgroup.le_centralizer_iff.mp hFcentU
    have hUleM : c.U ≤ w.M := by
      rw [← od.F_normalizer]
      exact hUcentF.trans (Subgroup.centralizer_le_normalizer (od.F : Set G))
    exact secondCase_a7_U_not_le_M hmin c w d hA7 hmodel hUleM
  have hZleK : Z ≤ od.K := by
    intro z hz
    obtain ⟨z0, hz0C, i, hiI, hzi⟩ :=
      fact_1_5_ii_decomposition od.s_involution
        (Nat.coprime_two_left.mpr hZodd) hsZ z hz
    have hz0one : z0 = 1 := by
      have hz0bot : z0 ∈ (⊥ : Subgroup G) := by
        rw [← hCZbot]
        exact hz0C
      exact Subgroup.mem_bot.mp hz0bot
    have hziEq : z = i := by simpa [hz0one] using hzi
    have hzinv : z ∈ invertedElements Z (od.s : G) := hziEq ▸ hiI
    change z ∈ (od.K : Set G)
    rw [od.K_inverted]
    exact ⟨⟨hZleU hz, hZleM hz⟩, hzinv.2⟩
  have hKleU : od.K ≤ c.U :=
    le_sup_left.trans (od.U_inter_M_eq.le.trans inf_le_left)
  have hUp : IsPGroup 3 c.U :=
    secondCase_a7_U_isPGroup_three hmin c w d hA7 hmodel
  obtain ⟨n, hUcard⟩ := IsPGroup.iff_card.mp hUp
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hdiv : Nat.card od.K ∣ Nat.card c.U :=
      Subgroup.card_dvd_of_le hKleU
    rw [od.K_card, hUcard, hn0] at hdiv
    norm_num at hdiv
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hkpos, hcenterCard⟩ :=
    IsPGroup.card_center_eq_prime_pow hUcard hnpos
  have hZcard : Nat.card Z = 3 ^ k := by
    calc
      Nat.card Z = Nat.card (Subgroup.center c.U) := by
        dsimp [Z]
        rw [Subgroup.card_map_of_injective c.U.subtype_injective]
      _ = 3 ^ k := hcenterCard
  have h3leZ : 3 ≤ Nat.card Z := by
    rw [hZcard]
    exact Nat.le_of_dvd (pow_pos (by norm_num) k)
      (dvd_pow_self 3 (by omega))
  have hZeqK : Z = od.K :=
    Subgroup.eq_of_le_of_card_ge hZleK (by rw [od.K_card]; exact h3leZ)
  exact hZeqK.symm

end CFSG.GorensteinWalter
