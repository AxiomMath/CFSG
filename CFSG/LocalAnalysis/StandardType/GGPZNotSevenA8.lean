module

public import CFSG.LocalAnalysis.StandardType.GGPZMultCore
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem ggPZ_not_halfSplit_seven_A8
    {G : Type} [Group G] [Finite G] {J Y : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hYperf : commutator ↥Y = ⊤) (hJY : J ≤ Y)
    (hJ : GGHasLabel ⟨.A, 4, 3 * a⟩ (↥J ⧸ Subgroup.center ↥J))
    (hY : GGHasLabel ⟨.A, 8, 1⟩ (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  have h151Jquot : 151 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel at hJ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hJ
    unfold LargeEvenRecipeLinear at hJ
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hJ
    let : Field K := hKfield
    let : Finite K := hKfin
    have hJadm : StatedLieAdmissible .PSL 5 2 (3 * a) :=
      ⟨Nat.prime_two, by omega, by norm_num,
        fun h => by simp only [Prod.mk.injEq] at h; omega,
        fun h => by simp only [Prod.mk.injEq] at h; omega⟩
    have hJmod : StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 5) K))
        .PSL 5 2 (3 * a) :=
      statedClassicalModel_linear 5 (3 * a) hKcard hJadm
    have hJmod' : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 5 2 (3 * a) :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hJmod
    have hJcard :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num : 0 < 5) hJmod'
    have hgnum : Nat.gcd 5 ((2 ^ (3 * a)) - 1) ∣
        (2 ^ (3 * a)) ^ 10 * ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) := by
      refine dvd_mul_of_dvd_right ?_ ((2 ^ (3 * a)) ^ 10)
      refine (Nat.gcd_dvd_right 5 ((2 ^ (3 * a)) - 1)).trans ?_
      have hx2 : (2 ^ (3 * a)) - 1 ∣ (2 ^ (3 * a)) ^ 2 - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow (2 ^ (3 * a)) 1 2
      exact hx2.trans
        (Finset.dvd_prod_of_mem (fun i => (2 ^ (3 * a)) ^ i - 1)
          (by simp : 2 ∈ Finset.Icc 2 5))
    have h151num : 151 ∣ (2 ^ (3 * a)) ^ 10 *
        ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) := by
      have h5 : 151 ∣ (2 ^ (3 * a)) ^ 5 - 1 := by
        have h1 : (151 : ℕ) ∣ 2 ^ 15 - 1 := by norm_num
        have h2 : (2 : ℕ) ^ 15 - 1 ∣ 2 ^ (15 * a) - 1 := by
          have h := Nat.sub_dvd_pow_sub_pow (2 ^ 15) 1 a
          simpa [pow_mul] using h
        have h3 : (2 : ℕ) ^ (15 * a) = (2 ^ (3 * a)) ^ 5 := by
          rw [← pow_mul]
          ring_nf
        rw [h3] at h2
        exact h1.trans h2
      exact dvd_mul_of_dvd_right
        (h5.trans (Finset.dvd_prod_of_mem (fun i => (2 ^ (3 * a)) ^ i - 1)
          (by simp : 5 ∈ Finset.Icc 2 5))) ((2 ^ (3 * a)) ^ 10)
    have hcop : ¬ 151 ∣ Nat.gcd 5 ((2 ^ (3 * a)) - 1) := by
      intro h
      exact (by norm_num : ¬ (151 : ℕ) ∣ 5)
        (h.trans (Nat.gcd_dvd_left 5 ((2 ^ (3 * a)) - 1)))
    have hcardN : Nat.card (↥J ⧸ Subgroup.center ↥J) =
        ((2 ^ (3 * a)) ^ 10 * ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1)) /
          Nat.gcd 5 ((2 ^ (3 * a)) - 1) := by
      rw [hJcard]
    rw [hcardN]
    have hdecomp : (2 ^ (3 * a)) ^ 10 *
        ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1) =
        (((2 ^ (3 * a)) ^ 10 * ∏ i ∈ Finset.Icc 2 5, ((2 ^ (3 * a)) ^ i - 1)) /
          Nat.gcd 5 ((2 ^ (3 * a)) - 1)) * Nat.gcd 5 ((2 ^ (3 * a)) - 1) :=
      (Nat.div_mul_cancel hgnum).symm
    have hsteps := h151num
    rw [hdecomp] at hsteps
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 151)).mp hsteps with h | h
    · exact h
    · exact absurd h hcop
  have h151J : 151 ∣ Nat.card ↥J :=
    h151Jquot.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  unfold GGHasLabel at hY
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hY
  unfold LargeEvenRecipeLinear at hY
  obtain ⟨KY, hKYfield, hKYfin, hKYcard, ⟨eY⟩⟩ := hY
  let : Field KY := hKYfield
  let : Finite KY := hKYfin
  have hYadm : StatedLieAdmissible .PSL 9 2 1 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hYmod : StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 9) KY)) .PSL 9 2 1 :=
    statedClassicalModel_linear 9 1 hKYcard hYadm
  have hYmod' : StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSL 9 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eY.symm hYmod
  obtain ⟨-, ⟨eY'⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hYmod'
  have hYcenter : Nat.card (Subgroup.center ↥Y) = 1 := by
    have hd := ggPZMult_card_dvd (Y := ↥Y) hYperf ⟨eY'⟩
    have hone : ((genericOrders .PSL 9 2 1).1 * (genericOrders .PSL 9 2 1).2) *
        ((exceptionalOrders .PSL 9 2 1).1 * (exceptionalOrders .PSL 9 2 1).2) = 1 := by
      norm_num [genericOrders, exceptionalOrders]
    rw [hone] at hd
    exact Nat.dvd_one.mp hd
  have hYquotcard : Nat.card (↥Y ⧸ Subgroup.center ↥Y) =
      2 ^ 36 * ∏ i ∈ Finset.Icc 2 9, (2 ^ i - 1) := by
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num : 0 < 9) hYmod']
    norm_num
  have hYcard : Nat.card ↥Y = 2 ^ 36 * ∏ i ∈ Finset.Icc 2 9, (2 ^ i - 1) := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Y)
    rw [hYcenter, mul_one] at hsplit
    rw [hsplit, hYquotcard]
  have hYnotdvd : ¬ 151 ∣ Nat.card ↥Y := by
    rw [hYcard]
    decide
  exact hYnotdvd (h151J.trans (Subgroup.card_dvd_of_le hJY))

end CFSG.StandardType

end
