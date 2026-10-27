module

import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.BRANCH.RankClassical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.PartOne.LIT CFSG.Open CFSG.RankThree.PartOne.BRANCH

theorem false_psl_two_five {T : Type} [Group T] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hmod : StatedClassicalModel T .PSL n 2 1) {q : ℕ} (hq37 : q = 3 ∨ q = 7) {D : Subgroup T}
    (hcard : Nat.card D = q ^ 5) : False := by
  have hT := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl
  have hdvd : q ^ 5 ∣ Nat.card T := hcard ▸ Subgroup.card_subgroup_dvd_card D
  rw [hT] at hdvd
  rcases hn with rfl | rfl <;> rcases hq37 with rfl | rfl <;> revert hdvd <;> decide

theorem false_psu_six_two_seven {T : Type} [Group T] (hmod : StatedClassicalModel T .PSU 6 2 1)
    {D : Subgroup T} (hcard : Nat.card D = 7 ^ 5) : False := by
  have hT := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  have hdvd : 7 ^ 5 ∣ Nat.card T := hcard ▸ Subgroup.card_subgroup_dvd_card D
  rw [hT] at hdvd
  revert hdvd
  decide

theorem false_F4_two_seven
    {T : Type} [Group T] (hmod : UntwistedChevalleyModel T .F4 2) {D : Subgroup T}
    (hcard : Nat.card D = 7 ^ 5) : False := by
  have hT := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmod
  have hdvd : 7 ^ 5 ∣ ordF4 2 := by
    rw [← hT, ← hcard]
    exact Subgroup.card_subgroup_dvd_card D
  revert hdvd
  decide

theorem false_tits_five
    {T : Type} [Group T] {f : ℕ} (hmod : ReeTitsModel T .Tits 2 f) {q : ℕ} (hq37 : q = 3 ∨ q = 7)
    {D : Subgroup T} (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T 2 f hmod
  have hT : Nat.card T = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  have hdvd : q ^ 5 ∣ 17971200 := by
    rw [← hT, ← hcard]
    exact Subgroup.card_subgroup_dvd_card D
  rcases hq37 with rfl | rfl <;> revert hdvd <;> decide

theorem false_suzuki_five {T : Type} [Group T] {f : ℕ} (hmod : SuzukiModel T 2 f) {q : ℕ}
    (hq : q.Prime) (hq37 : q = 3 ∨ q = 7) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hmod
  have : Fact q.Prime := ⟨hq⟩
  have : CharP K 2 := charP_two_of_card hK
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_charTwo (by rcases hq37 with rfl | rfl <;> rfl)
  let ψ : T →* GL (Fin 4) K := (suzukiGroup a K).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hF : IsElementaryAbelian q (D.map ψ) := by
    have := hD
    exact IsElementaryAbelian.map ψ
  obtain ⟨hcomm, hexp⟩ := isElementaryAbelian_data hF
  have : Finite (D.map ψ) := by
    have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 5 hq.ne_zero)
    exact Finite.of_equiv D (D.equivMapOfInjective ψ hψ).toEquiv
  have hb := card_le_pow_card_gl hq hqK (D.map ψ) hcomm hexp
  rw [Subgroup.card_map_of_injective hψ, hcard, Fintype.card_fin] at hb
  have := (Nat.pow_le_pow_iff_right hq.one_lt).mp hb
  omega

end CFSG.RankThree.PartOne.F106
