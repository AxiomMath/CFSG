module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UIsPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SylowCardEight
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal

namespace CFSG
end CFSG
open CFSG

/-! # The odd core is not contained in the second-case maximal subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, `U` is not contained in `M`.  Otherwise an order-eight
Sylow subgroup in `H ∩ M`, together with `H = S U`, would put all of `H` in
`M`. -/
public theorem secondCase_a7_U_not_le_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ¬ c.U ≤ w.M := by
  classical
  intro hUleM
  obtain ⟨SM, hSMcent, _SE, _hSEamb⟩ :=
    secondCase_centralizer_contains_sylow c w d
  obtain ⟨SM0, hSM0card⟩ :=
    secondCase_a7_sylow_card hmin c w d hA7 hmodel
  have hSMcard : Nat.card (SM : Subgroup w.M) = 8 :=
    (Nat.card_congr (Sylow.equiv SM0 SM).toEquiv).symm.trans hSM0card
  let T : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  have hTcard : Nat.card T = 8 := by
    rw [Subgroup.card_map_of_injective w.M.subtype_injective, hSMcard]
  have hScard : Nat.card (c.S : Subgroup G) = 8 :=
    secondCase_a7_S_card_eq_eight hmin c w d hA7 hmodel
  have hTleM : T ≤ w.M := Subgroup.map_subtype_le (SM : Subgroup w.M)
  have hTleH : T ≤ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent
  have hSleH : (c.S : Subgroup G) ≤ c.H :=
    centralizerSetup_S_le_H c
  have hUnormH : IsNormalIn c.U c.H := centralizerSetup_U_isNormalIn_H c
  have hUleH : c.U ≤ c.H := hUnormH.1
  have hTnormU : T ≤ Subgroup.normalizer (c.U : Set G) :=
    hTleH.trans (le_normalizer_of_isNormalIn hUnormH)
  have hSnormU : (c.S : Subgroup G) ≤
      Subgroup.normalizer (c.U : Set G) :=
    hSleH.trans (le_normalizer_of_isNormalIn hUnormH)
  have hUp : IsPGroup 3 c.U :=
    secondCase_a7_U_isPGroup_three hmin c w d hA7 hmodel
  have hTp : IsPGroup 2 T := SM.isPGroup'.map w.M.subtype
  have hSp : IsPGroup 2 (c.S : Subgroup G) := c.S.isPGroup'
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUTdisj : Disjoint c.U T :=
    IsPGroup.disjoint_of_ne 3 2 (by omega) c.U T hUp hTp
  have hUSdisj : Disjoint c.U (c.S : Subgroup G) :=
    IsPGroup.disjoint_of_ne 3 2 (by omega) c.U c.S hUp hSp
  have hUTcard : Nat.card (c.U ⊔ T : Subgroup G) =
      Nat.card c.U * Nat.card T :=
    card_sup_eq_mul_of_disjoint_of_le_normalizer c.U T hTnormU hUTdisj
  have hUScard : Nat.card (c.U ⊔ (c.S : Subgroup G) : Subgroup G) =
      Nat.card c.U * Nat.card (c.S : Subgroup G) :=
    card_sup_eq_mul_of_disjoint_of_le_normalizer
      c.U c.S hSnormU hUSdisj
  have hHSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU_proved hmin c
  have hHcard : Nat.card c.H =
      Nat.card c.U * Nat.card (c.S : Subgroup G) := by
    rw [← hHSU, sup_comm]
    exact hUScard
  have hcardEq : Nat.card c.H = Nat.card (c.U ⊔ T : Subgroup G) := by
    rw [hHcard, hUTcard, hScard, hTcard]
  have hUTeqH : c.U ⊔ T = c.H := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hUleH hTleH)
    rw [← hcardEq]
  have hHleM : c.H ≤ w.M := by
    rw [← hUTeqH]
    exact sup_le hUleM hTleM
  exact secondCase_H_not_le_M hmin c w hHleM

end CFSG.GorensteinWalter
