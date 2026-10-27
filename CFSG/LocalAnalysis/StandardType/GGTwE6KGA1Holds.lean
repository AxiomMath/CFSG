module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Compat
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1O0
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1O2
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1O3
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1O4
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1RankSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1TIn
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeToralCentHolds

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent CFSG.Open

private theorem holds_commute_of_mem_normalizer_zpowers {G : Type*} [Group G] {t : G}
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) {x : G}
    (hx : x ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :
    t * x = x * t := by
  have hmem : x * t * x⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.1 hx t).1 (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hne : x * t * x⁻¹ ≠ 1 := fun h => ht1 (by
    have h' : x⁻¹ * (x * t * x⁻¹) * x = 1 := by rw [h]; group
    rwa [show x⁻¹ * (x * t * x⁻¹) * x = t by group] at h')
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact ht2
  have heq : x * t * x⁻¹ = t := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact absurd (by rw [← hk, hm, ← two_mul, zpow_mul, h2, one_zpow]) hne
    · rw [← hk, hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  calc t * x = (x * t * x⁻¹) * x := by rw [heq]
    _ = x * t := by group

theorem exists_overgroup_of_inf_twInndiagAut_eq_bot (h84 : GGTwE6ThreeToralTypeMinusOneInput)
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hΦinj : Function.Injective Φ) (hΦrange : Φ.range = LayerSixE.twInndiagAut f)
    (hΦc : ∀ (c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (hc : baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ TwistedDiag.Rgrp Ω Fr),
      Φ ⟨baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω) (c : ModGL TwistTag.E6.tag
        (GaloisField 2 (2 * f))), hc⟩ = MulAut.conj c)
    {X U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    (hXI : X ≤ LayerSixE.twInndiagAut f) (hel : IsElemAbelian 3 X) (hc : Nat.card X = 3 ^ 4)
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hXU : X ≤ Subgroup.normalizer (U : Set _))
    (hUI : U ⊓ LayerSixE.twInndiagAut f = ⊥) :
    ∃ Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))),
      Y ≤ LayerSixE.twInndiagAut f ∧ X ≤ Y ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6 := by
  classical
  obtain ⟨t, ht2, htI, rfl⟩ := exists_zpowers_of_inf_twInndiagAut_eq_bot hf h3 hU hU2 hUI
  have ht1 : t ≠ 1 := fun h => htI (h ▸ one_mem _)
  have hXt : ∀ x ∈ X, t * x = x * t := fun x hx =>
    holds_commute_of_mem_normalizer_zpowers ht2 ht1 (hXU hx)
  have hXInn := le_inner_of_commute_outer_involution hf h3 ht2 htI hel hXI hXt
  obtain ⟨φ, Xh, hmap, hXhel, hXhcard, hXhP⟩ :=
    exists_conj_eq_map_conj_of_commute hf ht2 htI hel hXInn hXt
  set X' := X.map (MulAut.conj φ).toMonoidHom with hX'
  have hXhc : Nat.card Xh = 3 ^ 4 := hXhcard.trans hc
  have hX'I : X' ≤ LayerSixE.twInndiagAut f := by
    rw [hmap]
    exact (Subgroup.map_le_range _ _).trans le_sup_left
  have hX'el : IsElemAbelian 3 X' := hel.map _
  have hX'c : Nat.card X' = 3 ^ 4 := by
    rw [hX', Subgroup.card_map_of_injective (MulAut.conj φ).injective, hc]
  have htor : IsToralE6 Ω ((X'.comap Φ).map (TwistedDiag.Rgrp Ω Fr).subtype) := by
    rw [hmap, comap_map_conj_eq_map_baseChange hf h3 Ω Fr hFr Φ hΦinj hΦc Xh]
    exact isToralE6_map_baseChange_of_diagramMap_commute hf Ω hXhel hXhc hXhP
  obtain ⟨Y', hY'I, hX'Y', hY'el, hY'c⟩ :=
    exists_overgroup_of_isToral h84 hf h3 Ω Fr hFr Φ hΦinj hΦrange hX'I hX'el hX'c htor
  have hN := normal_twInndiagAut hf
  refine ⟨Y'.map (MulAut.conj φ⁻¹).toMonoidHom, ?_, ?_, hY'el.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hN.conj_mem y (hY'I hy) φ⁻¹
  · intro x hx
    refine ⟨φ * x * φ⁻¹, hX'Y' ⟨x, hx, rfl⟩, ?_⟩
    simp
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj φ⁻¹).injective, hY'c]

theorem ggTwE6ThreeTwoLocalRankSixInput_of_kg (h82 : GGTwE6ThreeTwoLocalInnToralInput)
    (h84 : GGTwE6ThreeToralTypeMinusOneInput) : GGTwE6ThreeTwoLocalRankSixInput := by
  intro f hf h3 X hel hXI hc hloc
  obtain ⟨U, hU, hU2, hXU⟩ := hloc
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  let Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 f
  have hFr : ∀ c, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  obtain ⟨Φ, hΦinj, hΦrange, hΦc⟩ := exists_rgrpAut_baseChange hf Ω Fr hFr
  by_cases hUI : U ⊓ LayerSixE.twInndiagAut f = ⊥
  · exact exists_overgroup_of_inf_twInndiagAut_eq_bot h84 hf h3 Ω Fr hFr Φ hΦinj hΦrange hΦc
      hXI hel hc hU hU2 hXU hUI
  · exact exists_overgroup_of_isToral h84 hf h3 Ω Fr hFr Φ hΦinj hΦrange hXI hel hc
      (isToralE6_of_inf_twInndiagAut_ne_bot h82 hf h3 Ω Fr hFr Φ hΦinj hΦrange hXI hel hc hU2
        hXU hUI)

theorem ggTwE6ThreeToralCentInput_of_kg (h82 : GGTwE6ThreeTwoLocalInnToralInput)
    (h84 : GGTwE6ThreeToralTypeMinusOneInput) : GGTwE6ThreeToralCentInput :=
  ggTwE6ThreeToralCentInput_of_rankSix (ggTwE6ThreeTwoLocalRankSixInput_of_kg h82 h84)

end CFSG.StandardType.NoOffTwE6Three
