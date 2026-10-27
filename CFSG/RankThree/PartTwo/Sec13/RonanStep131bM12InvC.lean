module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

open M12Inv in
theorem invPartC_holds : InvPartC := by
  intro G _ _ A c L E F a b R Y hY hbY hEF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : Sec13Data G F b Y := hY.hD
  have hEe := hY.hCfg.hEe
  have hE27 := hY.hCfg.hE27
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hD.isElemAbelian
  have hF27 : Nat.card F = 27 := hD.card_eq
  have hb3 : b ^ 3 = 1 := hEe.2 b hY.hbE
  have hb1 : b ≠ 1 := hD.ne_one
  have hc3 : c ^ 3 = 1 := hEe.2 c hY.hcE
  have hc1 : c ≠ 1 := hY.hCfg.hD.ne_one
  have hKb : Y ≤ Subgroup.centralizer ({b} : Set G) := hD.le_centralizer
  have hbc : ∀ y ∈ Y, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKb hy)
  have hdecomp : ∀ x ∈ E ⊔ F, ∃ (i : ℤ) (y : G), y ∈ Y ∧ x = b ^ i * y :=
    fun x hx => exists_zpow_mul_of_mem_zpowers_sup' hKb (hEF hx)
  have hdec : E = Subgroup.zpowers b ⊔ (E ⊓ Y) := by
    refine le_antisymm (fun e he => ?_) (sup_le (Subgroup.zpowers_le.mpr hY.hbE) inf_le_left)
    obtain ⟨i, y, hy, rfl⟩ := hdecomp e (Subgroup.mem_sup_left he)
    have hyE : y ∈ E := by
      have := E.mul_mem (E.inv_mem (E.zpow_mem hY.hbE i)) he
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers b i))
      (Subgroup.mem_sup_right ⟨hyE, hy⟩)
  have hcommbK : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ (E ⊓ Y : Subgroup G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hbc y hy.2).symm j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommbK
  have hinf : Subgroup.zpowers b ⊓ (E ⊓ Y) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (zpowers_inf_eq_bot' hb3 hbY).le)
  have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hE9 : Nat.card (E ⊓ Y : Subgroup G) = 9 := by
    rw [← hdec, hE27, hinf, Subgroup.card_bot, mul_one, hcardb] at hcard
    omega
  refine ⟨hdec, hE9, ?_⟩
  have hnc : ∃ f ∈ F, ∃ e ∈ E, f * e ≠ e * f := by
    by_contra hcon
    push Not at hcon
    have hsup := isElemAbelian_sup_of_commute hEe hFe (fun e he f hf => (hcon f hf e he).symm)
    have hEleF : E ≤ F := by
      have h := hD.mem_partTwoF.2.1 _ hsup le_sup_right
      calc E ≤ E ⊔ F := le_sup_left
        _ = F := h
    have hEeqF : E = F := Subgroup.eq_of_le_of_card_ge hEleF (by rw [hF27, hE27])
    exact hY.haE (hEeqF ▸ hY.haF)
  obtain ⟨f, hf, e, he, hfe⟩ := hnc
  have hzc : f * e * f⁻¹ * e⁻¹ ∈ Subgroup.zpowers c := hY.hcomm f hf e he
  have hz1 : f * e * f⁻¹ * e⁻¹ ≠ 1 := by
    intro h
    apply hfe
    have h2 : f * e * f⁻¹ = e := mul_inv_eq_one.mp h
    calc f * e = f * e * f⁻¹ * f := by group
      _ = e * f := by rw [h2]
  obtain ⟨i, f₁, hf₁, hfdef⟩ := hdecomp f (Subgroup.mem_sup_right hf)
  obtain ⟨j, e₁, he₁, hedef⟩ := hdecomp e (Subgroup.mem_sup_left he)
  have hz_eq : f * e * f⁻¹ * e⁻¹ = ⁅f₁, e₁⁆ := by
    have hb_f : Commute b f₁ := (hbc f₁ hf₁).symm
    have hb_e : Commute b e₁ := (hbc e₁ he₁).symm
    rw [hfdef, hedef, ← commutatorElement_def]
    exact commutatorElement_mul_mul' (hb_f.zpow_left i) (Commute.zpow_zpow_self b i j)
      (hb_e.zpow_left i) (hb_f.zpow_left j) (hb_e.zpow_left j)
  have hzY : f * e * f⁻¹ * e⁻¹ ∈ Y := by
    rw [hz_eq, commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hf₁ he₁) (Y.inv_mem hf₁)) (Y.inv_mem he₁)
  have hz3 : orderOf (f * e * f⁻¹ * e⁻¹) = 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers c) hzc
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have heq : Subgroup.zpowers (f * e * f⁻¹ * e⁻¹) = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, orderOf_eq_prime hc3 hc1])
  have hcz : c ∈ Subgroup.zpowers (f * e * f⁻¹ * e⁻¹) := heq ▸ Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr hzY hcz

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
