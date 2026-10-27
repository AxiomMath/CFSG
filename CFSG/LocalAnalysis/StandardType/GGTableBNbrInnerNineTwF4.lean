module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne.SEITZ7

namespace NbrInnerNine

theorem not_dvd_twF4_cofactor_of_dvd_sub {q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : p ∣ q - 1) :
    ¬ p ∣ q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have := Fact.mk hp
  intro h
  have hq1 : (q : ZMod p) = 1 := by
    have h1 : ((q - 1 : ℕ) : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hpq
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_eq_zero] at h1
    exact h1
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h4 : q ^ 2 ≤ q ^ 4 := by nlinarith [Nat.mul_le_mul h2 h2]
  have hc : ((q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) : ZMod p) =
      ((4 : ℕ) : ZMod p) := by
    push_cast [Nat.cast_sub h2, Nat.cast_sub h4]
    rw [hq1]
    norm_num
  have h0 : ((q ^ 10 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) : ZMod p) =
      0 := by rw [ZMod.natCast_eq_zero_iff]; exact h
  rw [h0, eq_comm, ZMod.natCast_eq_zero_iff] at hc
  have h22 : p ∣ 2 ^ 2 := by norm_num; exact hc
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h22))

theorem factorization_twF4_eq_of_dvd_sub {q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : p ∣ q - 1) :
    (q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
        (q ^ 4 - q ^ 2 + 1)).factorization p =
      (q * (q ^ 2 - 1)).factorization p + (q * (q ^ 2 - 1)).factorization p := by
  have hR := not_dvd_twF4_cofactor_of_dvd_sub hp hp2 hq hpq
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


theorem card_le_sq_twF4_of_dvd_sub {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ (2 * a + 1) - 1)
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
    exact factorization_twF4_eq_of_dvd_sub hp hp2 hq2 hpq
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact TableBExcSmallRest.card_le_sq_of_prod_sl2 μ hμ hp hp2 hord hE

theorem largeEvenLabelAll_card_lt_twF4_sub {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpn
  subst ht
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_twF4_equiv ha K hK
  have hZ := TableBExcSmallRest.center_eq_bot_of_mulEquiv e
    (ReeTag.large_Ree_fixed_group_center_trivial _ K hK)
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hI := chevIDImage_subset_inn_twF4 ha K hK
  refine TableBExcSmallRest.card_lt_of_subset_inn hZ (fun A hA =>
    TableBExcSmallRest.card_lt_of_mulEquiv e (fun E hE =>
      (card_le_sq_twF4_of_dvd_sub ha K hK hp hp2 (by rw [hna]; exact hpn) hE).trans_lt
        (Nat.pow_lt_pow_right hp.one_lt (by norm_num))) hA) (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end TwF4

end NbrInnerNine

end CFSG.StandardType

end
