module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcAdj
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGLayerInnerModelOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ =>
        ∀ r : R, GGModelLayerCyclic p (MulAut.conj r))

section TriD4


theorem finite_ggPSections_recipe_triD4 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Finite (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) ∧
      GGPSections p
        (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e₁⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK hσ
  have hKD : Nat.card K = (2 ^ n) ^ TwistTag.D4.order := hK
  have hC0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom).map
        (adjointGroup CFSG.LieType.Steinberg.TwistedD4.d4 K).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hn K hKD σ.toRingHom
      hσ).2.2.1.symm.trans
      (CFSG.LieType.Steinberg.TwistedD4.commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 hK hσ)
  let e₂ : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hC0.symm)
  have hsec : GGPSections p (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) := by
    intro E _ _ η hη hker hpk
    obtain ⟨s, hs, -⟩ := CFSG.SectionRank.triality_even_central_odd_extension_splitting hσ3 hη
      hker (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
        (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk)))
    exact ⟨s, hs⟩
  exact ⟨Finite.of_equiv _ e₁.symm.toEquiv,
    LayerCyc.ggPSections_of_mulEquiv (e₂.trans e₁.symm) hsec⟩

theorem largeEvenLabelAll_layerCenterCyclic_triD4
    (h : GGLayerInnerModelOn fun lab => lab.tag = .triD4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  intro Q hQ
  have hQ' := h p lab hp hp2 hlab hs ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hn
  subst ht
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hmod⟩ := hQ'
  refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
  obtain ⟨hfin, hsec⟩ := finite_ggPSections_recipe_triD4 hn K hK hp hp2
  exact ggLayerCenterCyclic_of_mulEquiv_inn hp (MulEquiv.refl _)
    (TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK)
    (LayerCycExc.commutator_eq_top_of_simple hsimple hnab)
    hsec (hmod hsimple hnab)

end TriD4

section TwF4


theorem finite_ggPSections_recipe_twF4 {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) ∧
      GGPSections p (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨e₁⟩ := TableBExcSmallRest.nonempty_twF4_equiv ha K hK
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  let e₂ : CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K a ≃*
      CFSG.LieType.Ree.ReeTag.F4.reeGamma K a :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr CFSG.LieType.Ree.LargeReeInvolution.map_reeFixed_eq_reeGamma)
  have hsec : GGPSections p (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K a) := by
    intro E _ _ η hη hker hpk
    exact CFSG.SectionRank.LargeRee.large_ree_section_of_suzuki
      CFSG.SectionRank.LargeRee.suzukiBlockInputs ha hK hη hker
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk)))
  exact ⟨Finite.of_equiv _ e₁.symm.toEquiv,
    LayerCyc.ggPSections_of_mulEquiv (e₂.trans e₁.symm) hsec⟩

theorem largeEvenLabelAll_layerCenterCyclic_twF4
    (h : GGLayerInnerModelOn fun lab => lab.tag = .twF4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  intro Q hQ
  have hQ' := h p lab hp hp2 hlab hs ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hmod⟩ := hQ'
  refine ⟨K, i1, i2, hK, hq, fun hsimple hnab => ?_⟩
  obtain ⟨hfin, hsec⟩ := finite_ggPSections_recipe_twF4 ha K hK hp hp2
  exact ggLayerCenterCyclic_of_mulEquiv_inn hp (MulEquiv.refl _)
    (chevIDImage_subset_inn_twF4 ha K hK) (LayerCycExc.commutator_eq_top_of_simple hsimple hnab)
    hsec (hmod hsimple hnab)

end TwF4

end CFSG.StandardType

end
