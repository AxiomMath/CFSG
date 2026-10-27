module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcHead
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4WeylLarge
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4WeylThree
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.RankThree.SteinbergR3ELargeReeOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem center_twF4Row_eq_bot
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H a K)) = ⊥ := by
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma (K := K) (a := a) ha hK
  have hZree : Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) = ⊥ :=
    CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hK
  rw [eq_bot_iff]
  intro z hz
  have h1 : eR z ∈ Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨y, rfl⟩ := eR.surjective g
    rw [← map_mul, ← map_mul, hz y]
  rw [hZree, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact eR.injective (h1.trans (map_one eR).symm)

theorem ggCenterPrime_twF4Row
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) : GGCenterPrime p (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma (K := K) (a := a) ha hK
  have hZree : Subgroup.center ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) = ⊥ :=
    CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hK
  let e : LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃*
      LargeEvenCenterQuot (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) :=
    eR.trans (centerQuotEquivOfBot hZree).symm
  intro L' _ _ ψ hψ hker hperf hdvd
  have hkc : ψ.ker = Subgroup.center L' :=
    TableBUR.ker_eq_center_of_surjective hψ hker (center_twF4Row_eq_bot ha hK)
  let θ : L' ⧸ Subgroup.center L' ≃* LargeEvenCenterQuot (LargeEvenTwF4H a K) :=
    (QuotientGroup.quotientMulEquivOfEq hkc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have h1 := gff_center_eq_bot_ree (K := K) (a := a) ha hK hperf (θ.trans e)
  rw [h1, Subgroup.card_bot] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

theorem two_dvd_card_twF4Row
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    2 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma (K := K) (a := a) ha hK
  have h2 : 2 ∣ (2 ^ (2 * a + 1)) ^ 12 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  rw [Nat.card_congr eR.toEquiv,
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).1]
  exact ((((h2.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _

theorem ggTorusNoLineTwo_twF4Row_of_irred
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hirr : GGSCWeylIrredTwoLU4 p ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) :
    GGTorusNoLineTwo p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma (K := K) (a := a) ha hK
  exact ggTorusNoLineTwo_of_scWeylIrredTwoLU4 hp (center_twF4Row_eq_bot ha hK)
    (fun _ hφ _ => chevIDImage_subset_inn_twF4 ha K hK hφ) (ggCenterPrime_twF4Row ha hK hp)
    (ggSCWeylIrredTwoLU4_of_mulEquiv eR hirr)

theorem rowPlainTwo_twF4Row_recipe_of_irred
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hirr : GGSCWeylIrredTwoLU4 p ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) :
    GGNbrWeylRowPlainTwo p 0 (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) :=
  ⟨fun g => conj_mem_chevIDImage _ g, TypeA.ggTorusLift_zero (two_dvd_card_twF4Row ha hK),
    fun _ _ => ggTorusNoLineTwo_twF4Row_of_irred ha hK hp hirr⟩

theorem largeEvenLabelAll_rowPlainTwo_twF4Add_of_irred
    (hIrr : ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K]
      [CharP K CFSG.LieType.Ree.ReeTag.F4.prime], Nat.card K = 2 ^ (2 * a + 1) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ (2 * a + 1) + 1 →
        GGSCWeylIrredTwoLU4 p ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpq⟩ := h
  dsimp only at ht hpq
  subst ht
  dsimp only [LargeEvenInLambda2] at hlab
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  subst hk
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
  rw [show (2 * k + 1 - 1) / 2 = k by omega] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  exact ⟨K, hf, hfin, hK, hQ', rowPlainTwo_twF4Row_recipe_of_irred (by omega) hK hp
    (hIrr k (by omega) K hK p hp hp2 hpq)⟩

theorem ggSCWeylIrredTwoLU4_reeGamma_twF4Add
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ (2 * a + 1) + 1) :
    GGSCWeylIrredTwoLU4 p ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
  by_cases h3 : p = 3
  · subst h3
    exact ggSCWeylIrredTwoLU4_reeGamma_twF4Three a hK
  · have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have h2 := hp.two_le
    exact ggSCWeylIrredTwoLU4_reeGamma_twF4Large ha hK hp (by omega) hpq

theorem largeEvenLabelAll_rowPlainTwo_twF4Add
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) :=
  largeEvenLabelAll_rowPlainTwo_twF4Add_of_irred
    (fun a ha K _ _ _ hK p hp hp2 hpq =>
      ggSCWeylIrredTwoLU4_reeGamma_twF4Add a ha K hK p hp hp2 hpq) hp hp2 hlab h

theorem odd_div_twF4Row {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) (hd : p ∣ lab.n) : Odd (lab.n / p) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hd ⊢
  subst ht
  dsimp only [LargeEvenInLambda2] at hlab
  obtain ⟨-, -, hodd, -⟩ := hlab
  have he : n = p * (n / p) := (Nat.mul_div_cancel' hd).symm
  rw [he] at hodd
  exact (Nat.odd_mul.mp hodd).2

theorem ggFieldKLevel_twF4AddLarge_of
    (hRowAll : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n + 1 → LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0))
    (hFix : GGFieldFixKnown fun p lab => lab.tag = .twF4 ∧ 3 ≤ lab.n / p)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTwF4AddLabel p lab → 3 ≤ lab.n / p →
        LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS h3
  refine ggFieldKLevel_of_fixKnownRowTwo
    (S := fun p lab => LargeEvenInLambda2 lab ∧ GGFieldOtherTwF4AddLabel p lab ∧ 3 ≤ lab.n / p)
    (Rw := fun p lab => lab.tag = .twF4 ∧ (p.Prime → p ∣ 2 ^ lab.n + 1)) ?_ ?_ ?_ ?_ ?_
    hpc hconj hcen hinn p lab hp hp2 hlab ⟨hlab, hS, h3⟩
  · rintro p lab ⟨-, ⟨hd, ht, hpq⟩, -⟩
    exact ⟨hd, ⟨ht, fun _ => hpq⟩, ⟨ht, fun hp => (ggFermat_dvd_two_pow_add_one_iff hp hd).mp hpq⟩⟩
  · rintro p lab - ⟨hlab, ⟨hd, ht, -⟩, h3⟩
    have hodd := odd_div_twF4Row hlab ht hd
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht h3 hodd ⊢
    subst ht
    dsimp only [LargeEvenInLambda2] at hlab ⊢
    obtain ⟨-, hl, -, -⟩ := hlab
    exact ⟨by omega, hl, hodd, h3⟩
  · rintro p lab ⟨ht, -⟩
    refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rw [ht] at h' <;> cases h'
  · rintro p lab hp hp2 hlab ⟨-, ⟨-, ht, -⟩, h3⟩
    exact hFix p lab hp hp2 hlab ⟨ht, h3⟩
  · rintro p lab hp hp2 hlab ⟨ht, hpq⟩
    exact hRowAll p lab hp hp2 hlab ⟨ht, hpq hp⟩

end CFSG.StandardType

end
