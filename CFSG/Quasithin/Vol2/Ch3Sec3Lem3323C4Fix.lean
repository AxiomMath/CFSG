module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace C4Fix3323

variable {G : Type} [Group G]

theorem card_Q_of_case1 {T R L : Subgroup G}
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (h1 : IsC134Case1 (L ⊔ T) R L) : Nat.card ↥(c134Q (L ⊔ T) L) = 8 := by
  obtain ⟨-, nF, F, _, _, hFc, -, α', hα's, hα'k, β, hβs, hβk, -⟩ := h1
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ ⟨hα's, hα'k⟩)
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card, hF]
  simp

theorem card_Q_ge_of_case4Corr [Finite G] {T R L : Subgroup G}
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (h4 : CFSG.Quasithin.C134CorrLocal.IsC134Case4Corr (L ⊔ T) R L) :
    32 ≤ Nat.card ↥(c134Q (L ⊔ T) L) := by
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hE, hZQ, hCU, hU, -⟩, -⟩ := h4
  set Q := c134Q (L ⊔ T) L with hQ
  set C := c134CQ (L ⊔ T) L with hC
  set U := ⁅centerOf Q, L⁆ with hUdef
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  have hn : n = 1 := by
    have h2n : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF, pow_one]
    exact Nat.pow_right_injective (le_refl 2) h2n
  subst hn
  obtain ⟨hC4, -⟩ := C45.isE2_card_sq hE
  obtain ⟨-, -, β, hβs, hβk, -⟩ := hU
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hU8 : Nat.card ↥U = 8 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have hCZ : C ≤ centerOf Q := hZQ ▸ le_sup_left
  have hUZ : U ≤ centerOf Q := hZQ ▸ le_sup_right
  have hCN : C ≤ Subgroup.normalizer (U : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (hCZ ha).2 b (hUZ hb).1))
  have hprod := C45.card_sup_mul_card_inf hCN
  rw [hCU, Subgroup.card_bot, mul_one, hC4, hU8] at hprod
  have hle : Nat.card ↥(C ⊔ U) ≤ Nat.card ↥Q :=
    Subgroup.card_le_of_le ((sup_le hCZ hUZ).trans inf_le_left)
  omega

variable [Finite G] {T M L D : Subgroup G}

end C4Fix3323

end CFSG.Quasithin.H13
