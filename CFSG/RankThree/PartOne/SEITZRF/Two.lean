module

public import CFSG.RankThree.PartOne.SEITZRF.Main
public import CFSG.RankThree.PartOne.SEITZRF.SL2Two
public import CFSG.RankThree.PartOne.SEITZRF.SzTwo
public import CFSG.RankThree.PartOne.SEITZRF.LeviRat
public import CFSG.RankThree.PartOne.SEITZRF.FusTwo

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.RankThree.PartOne.CTP (fixedSubgroup)


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem card_fixSubfield_eq_two (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (hβ : orderOf β = 2 * a + 1) : Nat.card (fixSubfield β) = 2 := by
  obtain ⟨-, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK β
  rw [hβ, Nat.div_self (by omega), pow_one] at hcard
  exact hcard

theorem reeGamma_le_of_overgroup_two_odd
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : (2 * a + 1).Prime) (β : K ≃+* K)
    (hβ : orderOf β = 2 * a + 1) {H : Subgroup (ModGL F4.tag K)}
    (hHΓ : H ≤ F4.reeGamma K a) (hRH : Rf K a β ≤ H) (hHR : ¬ H ≤ Rf K a β) :
    F4.reeGamma K a ≤ H := by
  have hk := card_fixSubfield_eq_two hK β hβ
  refine reeGamma_le_of_overgroup_of_parts ha hK β hp hβ
    (fun Y hY hRY s hs hsY => eq_rankOneGroupOne_of_sylowA_mem_two hK β hk hp hY hRY hs hsY)
    (fun Y hY hRY b c hbc hbcY =>
      eq_rankOneGroupTwo_of_sylowB_mem_two ha hK β hk hp hY hRY hbc hbcY)
    (fun H' hRH' hU' => Y1_le_Rf_of_inf_le ha hK β hRH' hU')
    (fun H' hRH' hU' => Y2_le_Rf_of_inf_le ha hK β hRH' hU')
    (fun x hx hx2 hx1 =>
      exists_conj_of_involution_Rf_two_odd hK β hp (by omega) hβ hk hx hx2 hx1)
    hHΓ hRH hHR

theorem reeGamma_le_of_overgroup_two
    (ha2 : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : (2 * a + 1).Prime) (β : K ≃+* K)
    (hβ : orderOf β = 2 * a + 1) {H : Subgroup (ModGL F4.tag K)}
    (hHΓ : H ≤ F4.reeGamma K a) (hRH : Rf K a β ≤ H) (hHR : ¬ H ≤ Rf K a β) :
    F4.reeGamma K a ≤ H :=
  reeGamma_le_of_overgroup_two_odd (by omega) hK hp β hβ hHΓ hRH hHR

theorem subfieldPairReeF4Two_holds :
    SubfieldPairReeF4Two := by
  intro a ha513 K _ _ _ hK β hβ g hne
  have ha2 : 2 ≤ a := by omega
  have hp : (2 * a + 1).Prime := by
    rcases ha513 with h | h <;> rw [h] <;> norm_num
  exact closure_eq_top_of_maximal β g hne fun _ hHΓ hRH hHR =>
    reeGamma_le_of_overgroup_two ha2 hK hp β hβ hHΓ hRH hHR

theorem subfieldPairReeF4_holds :
    SEITZ2.SubfieldPairReeF4 :=
  subfieldPairReeF4_of_two subfieldPairReeF4Two_holds

end CFSG.RankThree.PartOne.SEITZRF
