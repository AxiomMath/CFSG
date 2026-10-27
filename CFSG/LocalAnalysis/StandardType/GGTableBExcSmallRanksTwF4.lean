module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne.SEITZ7

namespace TableBExcSmallRanks

theorem not_dvd_twF4_cofactor {q p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : p ∣ q + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have hq1 : (q : ℤ) ≡ -1 [ZMOD p] := by
    apply Int.ModEq.symm
    apply (Int.modEq_iff_dvd).mpr
    have : ((q + 1 : ℕ) : ℤ) = (q : ℤ) - (-1) := by push_cast; ring
    rw [← this]
    exact Int.natCast_dvd_natCast.mpr hpq
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h4 : q ^ 2 ≤ q ^ 4 := by nlinarith [Nat.mul_le_mul h2 h2]
  have hnd : ¬ p ∣ 12 := by
    intro h
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (p : ℤ) ∣ (-1 : ℤ) - q := hq1.dvd
    have h3 : (p : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.mpr h
    have h4' : (p : ℤ) ∣ 1 := by
      have := dvd_add h1 h3
      rw [show (-1 : ℤ) - q + q = -1 by ring] at this
      exact (dvd_neg).mp this
    have : p ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using h4')
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · have hR : ((q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) : ℤ) ≡
        12 [ZMOD p] := by
      have e : ((q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) : ℤ) =
          (q : ℤ) ^ 10 * ((q : ℤ) ^ 2 + 1) ^ 2 * ((q : ℤ) ^ 2 - q + 1) *
            ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) := by
        push_cast [Nat.cast_sub h2, Nat.cast_sub h4,
          Nat.cast_sub (by nlinarith : q ≤ q ^ 2 + 1)]
        ring
      rw [e]
      calc (q : ℤ) ^ 10 * ((q : ℤ) ^ 2 + 1) ^ 2 * ((q : ℤ) ^ 2 - q + 1) *
            ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) ≡
          (-1) ^ 10 * ((-1) ^ 2 + 1) ^ 2 * ((-1) ^ 2 - (-1) + 1) * ((-1) ^ 4 - (-1) ^ 2 + 1)
            [ZMOD p] := by gcongr
        _ = 12 := by norm_num
    have h1 : (p : ℤ) ∣ 12 - _ := hR.dvd
    have h3 : (p : ℤ) ∣ ((q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) :
        ℤ) := Int.natCast_dvd_natCast.mpr h
    have h12 : (p : ℤ) ∣ ((12 : ℕ) : ℤ) := by
      have := dvd_add h1 h3
      rwa [sub_add_cancel] at this
    exact hnd (Int.natCast_dvd_natCast.mp h12)

theorem factorization_twF4_eq {q p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : p ∣ q + 1) :
    (q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
        (q ^ 4 - q ^ 2 + 1)).factorization p =
      (q * (q ^ 2 - 1)).factorization p + (q * (q ^ 2 - 1)).factorization p := by
  obtain ⟨-, hR⟩ := not_dvd_twF4_cofactor hp hp5 hq hpq
  set R := q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) with hRdef
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e : q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) = (q * (q ^ 2 - 1)) * (q * (q ^ 2 - 1)) * R := by
    rw [hRdef]
    have e1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [h1, h2]
      ring
    rw [e1]
    ring
  have hA : q * (q ^ 2 - 1) ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    exact mul_ne_zero (by omega) (by omega)
  have hR0 : R ≠ 0 := fun h => hR (h ▸ dvd_zero p)
  rw [e, Nat.factorization_mul (mul_ne_zero hA hA) hR0, Nat.factorization_mul hA hA,
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hR, add_zero]

section TwF4


@[expose] def GGTwF4ThreeRankInput : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) →
    ∀ E : Subgroup (ReeTag.F4.reeGamma K a), IsElemAbelian 3 E → Nat.card E < 3 ^ 3


theorem card_le_sq_twF4_of_five_le {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) + 1)
    {E : Subgroup (ReeTag.F4.reeGamma K a)} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  let ι₁ : SL2 K →* ReeTag.F4.reeGamma K a :=
    (Subgroup.inclusion (rankOneGroupOne_le_reeGamma' hK)).comp
      (rankOneEquivSL K a hK).toMonoidHom
  let ι₂ : SL2 K →* ReeTag.F4.reeGamma K a :=
    (Subgroup.inclusion (slSubB_le_reeGamma hK)).comp
      ((slSubBEquiv (K := K) (a := a)).toMonoidHom.comp (rankOneEquivSL K a hK).toMonoidHom)
  have hι₁ : ∀ A, (ι₁ A : ModGL ReeTag.F4.tag K) = (rankOneEquivSL K a hK A : ModGL _ K) :=
    fun A => rfl
  have hι₂ : ∀ A, (ι₂ A : ModGL ReeTag.F4.tag K) =
      (slSubBEquiv (K := K) (a := a) (rankOneEquivSL K a hK A) : ModGL _ K) := fun A => rfl
  have hcomm : ∀ A B, Commute (ι₁ A) (ι₂ B) := fun A B => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hι₁, hι₂]
    exact commute_rankOneGroupOne_slSubB hK _ (rankOneEquivSL K a hK A).2 _
      (slSubBEquiv (K := K) (a := a) (rankOneEquivSL K a hK B)).2)
  let μ : SL2 K × SL2 K →* ReeTag.F4.reeGamma K a := MonoidHom.noncommCoprod ι₁ ι₂ hcomm
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨A, B⟩ hAB
    have h1 : ι₁ A = (ι₂ B)⁻¹ := eq_inv_of_mul_eq_one_left hAB
    have hmem : (ι₁ A : ModGL ReeTag.F4.tag K) ∈ rankOneGroupOne K a ⊓ slSubB K a := by
      refine ⟨by rw [hι₁]; exact (rankOneEquivSL K a hK A).2, ?_⟩
      rw [h1, Subgroup.coe_inv, hι₂]
      exact (slSubB K a).inv_mem (slSubBEquiv (K := K) (a := a) (rankOneEquivSL K a hK B)).2
    rw [rankOneGroupOne_inf_slSubB ha hK, Subgroup.mem_bot] at hmem
    have hA : A = 1 := (rankOneEquivSL K a hK).injective (Subtype.ext (by
      rw [← hι₁, hmem, map_one]
      rfl))
    subst hA
    rw [map_one] at h1
    have h2 : ι₂ B = 1 := inv_eq_one.mp h1.symm
    have hB : B = 1 := (rankOneEquivSL K a hK).injective ((slSubBEquiv (K := K) (a := a)).injective
      (Subtype.ext (by rw [← hι₂, h2, map_one, map_one]; rfl)))
    subst hB
    rfl
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hord : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p =
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization p +
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization p := by
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K
      hK).1, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, hK]
    exact factorization_twF4_eq hp hp5 hq2 hpq
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact TableBExcSmallRest.card_le_sq_of_prod_sl2 μ hμ hp (by omega) hord hE

theorem ggTwF4RankInput_of_three (h3 : GGTwF4ThreeRankInput) :
    TableBExcSmallRest.GGTwF4RankInput := by
  intro a ha K _ _ _ hK p hp hpq E hE
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 a ha K hK E hE
  · have hp2 : p ≠ 2 := by
      rintro rfl
      have h1 : 2 ^ (2 * a + 1) + 1 = 2 * 2 ^ (2 * a) + 1 := by ring
      rw [h1] at hpq
      omega
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    exact (card_le_sq_twF4_of_five_le ha K hK hp hp5 hpq hE).trans_lt
      (Nat.pow_lt_pow_right hp.one_lt (by norm_num))

end TwF4

end TableBExcSmallRanks

end CFSG.StandardType
