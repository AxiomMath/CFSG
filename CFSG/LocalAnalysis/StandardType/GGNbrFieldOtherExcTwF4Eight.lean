module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4EightCore
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4Row
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4WeylThree
public import CFSG.LieType.Ree.ReeHolds
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate10009
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4
import CFSG.LieType.Multipliers.Tits
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Ree CFSG.LocalAnalysis.GLTheoremA

private theorem sq_mem_commutator_twF4Eight {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) (g : reeFixed ReeTag.F4 k 0) :
    g ^ 2 ∈ commutator (reeFixed ReeTag.F4 k 0) := by
  set T := CFSG.LieType.Simplicity.titsData k hk
  set N := commutator (reeFixed ReeTag.F4 k 0) with hN
  have htop := T.commutator_sup_zpowers_eq_top hk
  set Q := QuotientGroup.mk' N with hQ
  have hzp : Q g ∈ Subgroup.zpowers (Q T.g₁) := by
    have h1 : Q g ∈ (N ⊔ Subgroup.zpowers T.g₁).map Q :=
      Subgroup.mem_map_of_mem Q (htop ▸ Subgroup.mem_top g)
    rwa [Subgroup.map_sup, hQ, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers] at h1
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hzp
  have hg1 : Q T.g₁ ^ 2 = 1 := by
    rw [← map_pow, hQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact T.g₁_sq_mem
  have h2 : Q (g ^ 2) = 1 := by
    rw [map_pow, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg1,
      one_zpow]
  rw [hQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

private theorem mem_commutator_of_pow_three_twF4Eight {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) (g : reeFixed ReeTag.F4 k 0)
    (hg : g ^ 3 = 1) : g ∈ commutator (reeFixed ReeTag.F4 k 0) := by
  have h : g = (g ^ 2)⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ', hg]
  rw [h]
  exact inv_mem (sq_mem_commutator_twF4Eight hk g)

private theorem two_dvd_card_tits_twF4Eight
    {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    2 ∣ Nat.card ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := by
  have : Fact (Nat.card k = 2) := ⟨hk⟩
  rw [Nat.card_congr (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := k)).toEquiv,
    CFSG.Sporadic.Schreier.Tits.card_titsD]
  norm_num

private theorem ggCenterPrime_tits_twF4Eight
    {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) {p : ℕ}
    (hp : p.Prime) : GGCenterPrime p ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := by
  have : Fact (Nat.card k = 2) := ⟨hk⟩
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_of_mulEquiv_titsD
    (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := k))
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      ↥(commutator ↥(reeFixed ReeTag.F4 k 0))) = 1 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_unique]
  have hZT : Subgroup.center ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hk
  intro L' _ _ ψ hψ hker hperf hdvd
  have hZL : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have h1 : ψ z ∈ Subgroup.center ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZT, Subgroup.mem_bot] at h1
    exact h1
  have hkerZ : ψ.ker = Subgroup.center L' := le_antisymm hker hZL
  let e : L' ⧸ Subgroup.center L' ≃* ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hdiv := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hperf⟩ e
  rw [hM, Nat.dvd_one] at hdiv
  rw [hdiv] at hdvd
  exact hp.not_dvd_one hdvd

theorem ggFixDataTwo_twF4Eight_recipe
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    (hS : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H 1 K)))
    (hna : ∃ a b : LargeEvenCenterQuot (LargeEvenTwF4H 1 K), a * b ≠ b * a)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H 1 K))}
    (hf : f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H 1 K))
    (hord : orderOf f = 3) :
    GGFixDataTwo 3 0 (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H 1 K)) f := by
  have : CharP K ReeTag.F4.prime := CFSG.StandardType.charP_two_of_card hK
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hF : FQ.InnFree 3 (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H 1 K)) :=
    Y10GField.innFree_of_ggRawInnField (RawAutReeF4.ggRawInnField_twF4_of_diag le_rfl hK
      (ggTwistedF4DiagInput_holds 1 le_rfl K hK hS) hp.one_lt.ne') hS hna
  obtain ⟨b, hbp, k, _, _, _, hk, ⟨φ⟩⟩ :=
    FR.exists_fixSub_equiv_reeGamma le_rfl hK hp (by norm_num) _ hF f hf hord
  have hb0 : b = 0 := by omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hk
  have : IsSimpleGroup ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := gff_isSimpleGroup_tits hk2
  have : Group.IsPerfect ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) :=
    (CFSG.LieType.Simplicity.titsData k hk2).isPerfect hk2
  have hZG : Subgroup.center ↥(reeFixed ReeTag.F4 k 0) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : ReeTag.reeFixedEquivReeGamma k 0 z ∈ Subgroup.center (ReeTag.F4.reeGamma k 0) :=
      (MulEquivClass.apply_mem_center_iff _).2 hz
    rw [ReeTag.large_Ree_fixed_group_center_trivial 0 k hk, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2
      ((ReeTag.reeFixedEquivReeGamma k 0).injective (hz'.trans (map_one _).symm))
  have hZ : Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H 1 K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H 1 K))) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H 1 K)) :=
        h ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  refine ggFixDataTwo_twF4Eight_of_fixSub hp hZ (fun φ hφ => ?_)
    ((MulEquiv.subgroupCongr (Y10GField.ggFixSub_eq_fixSub f)).trans
      (φ.trans (ReeTag.reeFixedEquivReeGamma k 0).symm)) hZG inferInstance
    (Y10GField.exists_mul_ne_of_isPerfect _) (mem_commutator_of_pow_three_twF4Eight hk2)
    (two_dvd_card_tits_twF4Eight hk2) (ggCenterPrime_tits_twF4Eight hk2 hp)
    (ggSCWeylIrredTwoLU4_tits_twF4Three hk2)
  obtain ⟨r, hr⟩ := chevIDImage_subset_inn_twF4 le_rfl K hK hφ
  exact ⟨r, hr⟩

theorem largeEvenLabelAll_fixDataTwo_twF4Eight
    {lab : LargeEvenLabel} (h : lab.tag = .twF4 ∧ lab.n = 3) :
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ f ∈ F, orderOf f = 3 → GGFixDataTwo 3 0 I f := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hn⟩ := h
  dsimp only at ht hn
  subst ht hn
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
  rw [show (3 - 1) / 2 = 1 from rfl] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun hS hna f hf hord =>
    ggFixDataTwo_twF4Eight_recipe hK hS hna hf hord⟩

theorem ggFieldKLevel_twF4Eight
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twF4 ∧ lab.n = 3) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp 3) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hRow : LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo 3 0) :=
    largeEvenLabelAll_rowPlainTwo_twF4Add hp hp2 hlab ⟨h.1, by rw [h.2]; norm_num⟩
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown 3 0) :=
    hRow.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna =>
        ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_two hp (hn hs hna))⟩
  have hD4 : GGNotD4Three 3 lab := fun ⟨ht, _⟩ => by rw [h.1] at ht; cases ht
  have hD43 : ¬ (lab.tag = .triD4 ∧ 3 = 3) := fun ⟨ht, _⟩ => by rw [h.1] at ht; cases ht
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    (hpc 3 hp hp2 lab hlab hD4).mono fun _ _ _ _ h' => ggRawFieldCycW_of_pCyclic h'
  exact largeEvenLabelAll_fieldKLevelComp_twF4Eight_of_fixDataTwo hp hRK hCyc
    (hconj 3 hp hp2 lab hlab hD43) (hcen lab hlab) (hinn 3 hp hp2 lab hlab)
    (largeEvenLabelAll_fixDataTwo_twF4Eight h)

end CFSG.StandardType

end
