module

public import CFSG.LocalAnalysis.StandardType.GGPZMultCore
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LieType.Multipliers.U62Sylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

private theorem pzbe_151_dvd_ordPSL5 (a : ℕ) :
    151 ∣ ((2 ^ (3 * a)) ^ (5 * (5 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1)) / Nat.gcd 5 (2 ^ (3 * a) - 1) := by
  have hfactor : 151 ∣ (2 ^ (3 * a)) ^ 5 - 1 := by
    have hdvd : 15 ∣ 3 * a * 5 := ⟨a, by ring⟩
    have h15a : 151 ∣ 2 ^ (3 * a * 5) - 1 :=
      (by norm_num : 151 ∣ 2 ^ 15 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hdvd)
    rw [pow_mul] at h15a
    exact h15a
  have hnum : 151 ∣ (2 ^ (3 * a)) ^ (5 * (5 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) := by
    have hmem : 5 ∈ Finset.Icc 2 5 := by norm_num
    exact hfactor.trans
      ((Finset.dvd_prod_of_mem (fun i => (2 ^ (3 * a)) ^ i - 1) hmem).trans
        (dvd_mul_left _ _))
  have hgN : Nat.gcd 5 (2 ^ (3 * a) - 1) ∣ (2 ^ (3 * a)) ^ (5 * (5 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) := by
    have h1 : Nat.gcd 5 (2 ^ (3 * a) - 1) ∣ 2 ^ (3 * a) - 1 :=
      Nat.gcd_dvd_right 5 (2 ^ (3 * a) - 1)
    have h2 : 2 ^ (3 * a) - 1 ∣ (2 ^ (3 * a)) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ (3 * a)) 1 2
    have h3 : (2 ^ (3 * a)) ^ 2 - 1 ∣
        ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) :=
      Finset.dvd_prod_of_mem (fun i => (2 ^ (3 * a)) ^ i - 1)
        (by norm_num : 2 ∈ Finset.Icc 2 5)
    exact h1.trans (h2.trans (h3.trans (dvd_mul_left _ _)))
  have hnot : ¬ 151 ∣ Nat.gcd 5 (2 ^ (3 * a) - 1) := by
    intro h
    have h5 : 151 ∣ 5 := h.trans (Nat.gcd_dvd_left 5 (2 ^ (3 * a) - 1))
    norm_num at h5
  have heq : ((2 ^ (3 * a)) ^ (5 * (5 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1)) / Nat.gcd 5 (2 ^ (3 * a) - 1) *
      Nat.gcd 5 (2 ^ (3 * a) - 1) =
      (2 ^ (3 * a)) ^ (5 * (5 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) :=
    Nat.div_mul_cancel hgN
  rw [← heq] at hnum
  rcases (by norm_num : Nat.Prime 151).dvd_mul.mp hnum with h | h
  · exact h
  · exact absurd h hnot

private theorem pzbe_151_dvd_psl5_quotient {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    (hX : GGHasLabel ⟨.A, 4, 3 * a⟩ X) : 151 ∣ Nat.card X := by
  have hadm : StatedLieAdmissible .PSL 5 2 (3 * a) := by
    refine ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩
    · intro h
      have h8 : 8 ≤ 2 ^ (3 * a) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (3 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      have h2dvd : 2 ∣ 2 ^ (3 * a) := dvd_pow_self 2 (by omega)
      rw [h.2] at h2dvd
      norm_num at h2dvd
  unfold GGHasLabel at hX
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hX
  unfold LargeEvenRecipeLinear at hX
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  have hmod : StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) .PSL 5 2
      (3 * a) :=
    statedClassicalModel_linear 5 (3 * a) hKcard hadm
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl
    (show 0 < 5 by norm_num) hmod
  rw [Nat.card_congr e.toEquiv, hcard]
  exact pzbe_151_dvd_ordPSL5 a

private theorem pzbe_chevE6_of_hasLabel {X : Type} [Group X]
    (hX : GGHasLabel ⟨.E6, 0, 1⟩ X) : CFSG.Blueprint.ChevalleyExceptionalModel X .E6 2 1 := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  refine ⟨⟨Nat.prime_two, le_rfl, rfl⟩, ?_⟩
  obtain ⟨K', hK'f, hK'fin, hK'card, ⟨e'⟩⟩ :=
    untwistedChevalleyModel_largeEven (K := K) (q := 2) .E6 hKcard
  exact ⟨K', hK'f, hK'fin, hK'card, ⟨e.trans e'⟩⟩

theorem ggPZ_not_halfSplit_seven_E6
    {G : Type} [Group G] [Finite G] {J Y : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hYperf : commutator ↥Y = ⊤) (hJY : J ≤ Y)
    (hJ : GGHasLabel ⟨.A, 4, 3 * a⟩ (↥J ⧸ Subgroup.center ↥J))
    (hY : GGHasLabel ⟨.E6, 0, 1⟩ (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  have hJq : 151 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    pzbe_151_dvd_psl5_quotient ha hJ
  have hJcard : 151 ∣ Nat.card ↥J :=
    hJq.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  have hJYcard : Nat.card ↥J ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hJY
  have h151Y : 151 ∣ Nat.card ↥Y := hJcard.trans hJYcard
  have hYchev : CFSG.Blueprint.ChevalleyExceptionalModel (↥Y ⧸ Subgroup.center ↥Y) .E6 2 1 :=
    pzbe_chevE6_of_hasLabel hY
  have hYqcard : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = CFSG.Open.ordE6 (2 ^ 1) := by
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two (t := .E6) (f := 1) hYchev
  have hcenter : Nat.card (Subgroup.center ↥Y) = 1 := by
    have hrow :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.e6_row (p := 2) (f := 1) hYchev
    have hd := ggPZMult_card_dvd (Y := ↥Y) hYperf hrow.2
    have hprod : (genericOrders .E6 0 2 1).1 * (genericOrders .E6 0 2 1).2 *
        ((exceptionalOrders .E6 0 2 1).1 * (exceptionalOrders .E6 0 2 1).2) = 1 := by
      norm_num [genericOrders, exceptionalOrders]
    rw [hprod] at hd
    exact Nat.dvd_one.mp hd
  have hYsplit : Nat.card ↥Y = Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Y)
    rw [hcenter, mul_one] at h
    exact h
  have hnot : ¬ 151 ∣ CFSG.Open.ordE6 (2 ^ 1) := by norm_num [CFSG.Open.ordE6]
  rw [hYsplit, hYqcard] at h151Y
  exact hnot h151Y

end CFSG.StandardType

end
