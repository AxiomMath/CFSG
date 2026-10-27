module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

namespace LayerPDivExc

section Inner

variable {L : Type} [Group L] {G : Type} [Group G]

theorem range_inf_centralizer_eq_map {ψ : L →* G} (hinj : Function.Injective ψ) {y : G}
    {t : L} (hyt : (y, t) ∈ LayerFacts.ggConjPairs ψ) :
    ψ.range ⊓ Subgroup.centralizer {y} = (Subgroup.centralizer {t}).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨u, rfl⟩, hu⟩
    have hu' : ψ u * y = y * ψ u := Subgroup.mem_centralizer_singleton_iff.mp hu
    refine ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    have h1 : t * u * t⁻¹ = u := hinj (by
      rw [LayerFacts.mem_ggConjPairs.mp hyt u, ← hu', mul_inv_cancel_right])
    calc u * t = t * u * t⁻¹ * t := by rw [h1]
      _ = t * u := by group
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp hu
    refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : t * u * t⁻¹ = u := by rw [← hu', mul_inv_cancel_right]
    have h2 := LayerFacts.mem_ggConjPairs.mp hyt u
    rw [h1] at h2
    calc ψ u * y = y * ψ u * y⁻¹ * y := by rw [← h2]
      _ = y * ψ u := by group

theorem dvd_card_of_isComponentOf_inner_conj {ψ : L →* G} (hinj : Function.Injective ψ)
    (hZ : Subgroup.center L = ⊥) {p : ℕ} {y : G} (hy : y ^ p = 1) {t : L}
    (hyt : (y, t) ∈ LayerFacts.ggConjPairs ψ)
    (h : t ^ p = 1 → ∀ X : Subgroup L, IsComponentOf X (Subgroup.centralizer {t}) →
      p ∣ Nat.card X)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y})) :
    p ∣ Nat.card K := by
  have htp : t ^ p = 1 := by
    have h1 := (LayerFacts.ggConjPairs ψ).pow_mem hyt p
    rw [Prod.pow_mk, hy] at h1
    have h2 := LayerFacts.mem_center_of_mem_ggConjPairs_one hinj h1
    rwa [hZ, Subgroup.mem_bot] at h2
  rw [range_inf_centralizer_eq_map hinj hyt] at hK
  have hKr : K ≤ ψ.range := hK.1.trans (Subgroup.map_le_range ψ _)
  rw [← LayerPDiv.card_comap_of_le_range hinj hKr]
  exact h htp _ (isComponentOf_comap hinj hK)

end Inner

end LayerPDivExc

section Defs

@[expose] def GGExcPDivNonToralInput (τ : Tag) : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ a : adjointGroup τ (GaloisField 2 f), a ^ p = 1 →
      ¬ GGExcToral τ (GaloisField 2 f) (Subgroup.zpowers a) →
        ∀ X : Subgroup (adjointGroup τ (GaloisField 2 f)),
          IsComponentOf X (Subgroup.centralizer {a}) → p ∣ Nat.card X

end Defs

section Tags

theorem LayerPDivExc.dvd_card_of_isComponentOf_of_nonToral {τ : Tag} {f : ℕ} (hf : 1 ≤ f)
    (hq : CFSG.IsQuasisimple (adjointGroup τ (GaloisField 2 f))) (hW : GGWeylFamQuotSolvInput τ)
    (h : GGExcPDivNonToralInput τ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) {a : adjointGroup τ (GaloisField 2 f)} (ha : a ^ p = 1)
    {X : Subgroup (adjointGroup τ (GaloisField 2 f))}
    (hX : IsComponentOf X (Subgroup.centralizer {a})) : p ∣ Nat.card X := by
  by_cases ht : GGExcToral τ (GaloisField 2 f) (Subgroup.zpowers a)
  · have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    exact LayerPDivExc.dvd_card_of_isComponentOf_centralizer_toral hq hW hp hp2
      (by rw [hF]; exact LayerPDiv.dvd_sq_sub_one hpq) ha ht hX
  · exact h f hf p hp hp2 hpq a ha ht X hX

theorem ggLayerPDivTag_F4_of_nonToral (h : GGExcPDivNonToralInput .F4) : GGLayerPDivTag .F4 := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have hZ : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (le_bot_iff.mp (hker.trans hZ.le))
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.Adj.exists_mem_centralizer_F4 ψ hker hdiag)
  exact LayerPDivExc.dvd_card_of_isComponentOf_inner_conj hinj hZ hy ht
    (fun htp X hX => LayerPDivExc.dvd_card_of_isComponentOf_of_nonToral hadm.2.1
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 _) ggWeylFamQuotSolvInput_F4 h hp hp2 hpq
      htp hX) hK

theorem ggLayerPDivTag_E8_of_nonToral (hW : GGWeylFamQuotSolvInput .E8)
    (h : GGExcPDivNonToralInput .E8) : GGLayerPDivTag .E8 := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (le_bot_iff.mp (hker.trans hZ.le))
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.Adj.exists_mem_centralizer_E8 ψ hker hdiag)
  exact LayerPDivExc.dvd_card_of_isComponentOf_inner_conj hinj hZ hy ht
    (fun htp X hX => LayerPDivExc.dvd_card_of_isComponentOf_of_nonToral hadm.2.1
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 _) hW h hp hp2 hpq htp hX) hK

theorem ggLayerPDivTag_E7_of_nonToral (hW : GGWeylFamQuotSolvInput .E7)
    (h : GGExcPDivNonToralInput .E7) : GGLayerPDivTag .E7 := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have hZ : Subgroup.center (e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (le_bot_iff.mp (hker.trans hZ.le))
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.Minu.exists_mem_centralizer_E7 ψ hker hdiag)
  refine LayerPDivExc.dvd_card_of_isComponentOf_inner_conj hinj hZ hy ht
    (fun htp X hX => ?_) hK
  set e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)
  refine LayerPDivExc.dvd_card_of_isComponentOf_of_mulEquiv e (fun X' hX' => ?_) hX
  exact LayerPDivExc.dvd_card_of_isComponentOf_of_nonToral hadm.2.1
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (CFSG.LieType.CurtisTits.isQuasisimple_e7 _))
    hW h hp hp2 hpq (by rw [← map_pow]; exact (congrArg e htp).trans (map_one e)) hX'

end Tags

namespace LayerPDivExc

section Model

open scoped commutatorElement

variable {L C : Type*} [Group L] [Group C] {G : Type*} [Group G]

theorem mem_autFix_zpowers {α : MulAut C} {x : C} :
    x ∈ LayerSixE.autFix (Subgroup.zpowers α) ↔ α x = x := by
  refine ⟨fun h => h α (Subgroup.mem_zpowers α), fun h β hβ => ?_⟩
  have hle : Subgroup.zpowers α ≤ MulAction.stabilizer (MulAut C) x :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
  exact MulAction.mem_stabilizer_iff.mp (hle hβ)

theorem dvd_card_of_isComponentOf_model [Finite L] {π : L →* C} (hπ : Function.Surjective π)
    (hπker : π.ker ≤ Subgroup.center L) {ψ : L →* G} (hker : ψ.ker ≤ π.ker) {p : ℕ}
    (hp : p.Prime) {y : G} (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut C}
    (hα : LayerSixE.GGInduces π ψ y α)
    (h : ∀ X : Subgroup C, IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) →
      p ∣ Nat.card X)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {y})) :
    p ∣ Nat.card K := by
  have hψker : ψ.ker ≤ Subgroup.center L := hker.trans hπker
  have hHM : (ψ.range ⊓ Subgroup.centralizer {y}).comap ψ ≤
      (LayerSixE.autFix (Subgroup.zpowers α)).comap π := by
    intro u hu
    have hyu : ψ u * y = y * ψ u :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2
    rw [Subgroup.mem_comap, mem_autFix_zpowers]
    exact (hα u u (by rw [← hyu, mul_inv_cancel_right])).symm
  have hMH : ⁅(LayerSixE.autFix (Subgroup.zpowers α)).comap π,
      (LayerSixE.autFix (Subgroup.zpowers α)).comap π⁆ ≤
        (ψ.range ⊓ Subgroup.centralizer {y}).comap ψ := by
    rw [Subgroup.commutator_le]
    intro u₁ hu₁ u₂ hu₂
    have hz : ∀ {u u' : L}, u ∈ (LayerSixE.autFix (Subgroup.zpowers α)).comap π →
        ψ u' = y * ψ u * y⁻¹ → u⁻¹ * u' ∈ Subgroup.center L := by
      intro u u' hu hu'
      refine hπker ?_
      have hfix : α (π u) = π u := mem_autFix_zpowers.mp (Subgroup.mem_comap.mp hu)
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα u u' hu', hfix, inv_mul_cancel]
    obtain ⟨u₁', hu₁'⟩ := LayerSixE.exists_conj_eq hyN u₁
    obtain ⟨u₂', hu₂'⟩ := LayerSixE.exists_conj_eq hyN u₂
    have hconj : ψ ⁅u₁', u₂'⁆ = y * ψ ⁅u₁, u₂⁆ * y⁻¹ := by
      rw [map_commutatorElement, map_commutatorElement, hu₁', hu₂']
      simp only [commutatorElement_def]
      group
    have hc : ⁅u₁', u₂'⁆ = ⁅u₁, u₂⁆ := by
      calc ⁅u₁', u₂'⁆ = ⁅u₁ * (u₁⁻¹ * u₁'), u₂ * (u₂⁻¹ * u₂')⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅u₁, u₂⁆ := by
            rw [LayerSixE.commutatorElement_mul_central_left (hz hu₁ hu₁'),
              LayerSixE.commutatorElement_mul_central_right (hz hu₂ hu₂')]
    rw [hc] at hconj
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc ψ ⁅u₁, u₂⁆ * y = y * ψ ⁅u₁, u₂⁆ * y⁻¹ * y := by rw [← hconj]
      _ = y * ψ ⁅u₁, u₂⁆ := by group
  have hKr : K ≤ ψ.range := hK.1.trans inf_le_left
  have hKq : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK.2.2
  have hcomap : (K.subgroupOf ψ.range).comap ψ.rangeRestrict = K.comap ψ := by
    ext u
    simp [Subgroup.mem_subgroupOf]
  have hKtq : CFSG.IsQuasisimple ↥(⁅K.comap ψ, K.comap ψ⁆ : Subgroup L) := by
    have h1 := CFSG.RankThree.PartOne.isQuasisimple_derivedPreimage
      (MonoidHom.rangeRestrict_surjective ψ)
      (by rw [MonoidHom.ker_rangeRestrict]; exact hψker)
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKr).symm hKq)
    rwa [CFSG.RankThree.PartOne.derivedPreimage, hcomap] at h1
  have hKtψ : (⁅K.comap ψ, K.comap ψ⁆).map ψ = K := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hKr,
      LayerFacts.ggCommutator_eq_of_isQuasisimple hKq]
  have hKtπ : ¬ ⁅K.comap ψ, K.comap ψ⁆ ≤ π.ker := by
    intro hle
    obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hKtq
    exact hab (Subtype.ext (Subgroup.mem_center_iff.mp (hπker (hle a.2)) b).symm)
  have hsn1 : IsSubnormal ⁅K.comap ψ, K.comap ψ⁆ (K.comap ψ) :=
    LayerCores.ggSubnormal_of_normal (Subgroup.commutator_le_self _)
      fun u hu s hs => LayerSixE.conj_mem_commutator_self hu hs
  have hsn2 : IsSubnormal (K.comap ψ) ((ψ.range ⊓ Subgroup.centralizer {y}).comap ψ) :=
    LayerCores.ggSubnormal_comap ψ hK.2.1
  have hsn3 : IsSubnormal ((ψ.range ⊓ Subgroup.centralizer {y}).comap ψ)
      ((LayerSixE.autFix (Subgroup.zpowers α)).comap π) := by
    refine LayerCores.ggSubnormal_of_normal hHM fun u hu s hs => ?_
    have e : u * s * u⁻¹ = ⁅u, s⁆ * s := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hMH (Subgroup.commutator_mem_commutator hu (hHM hs))) hs
  have hsn := LayerCores.ggSubnormal_map π
    (LayerCores.ggSubnormal_trans hsn1 (LayerCores.ggSubnormal_trans hsn2 hsn3))
  rw [Subgroup.map_comap_eq_self_of_surjective hπ] at hsn
  have hY : IsComponentOf ((⁅K.comap ψ, K.comap ψ⁆).map π)
      (LayerSixE.autFix (Subgroup.zpowers α)) :=
    ⟨LayerCores.ggSubnormal_le hsn, hsn,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_map hKtq π hKtπ)⟩
  have hpKt : p ∣ Nat.card ↥(⁅K.comap ψ, K.comap ψ⁆ : Subgroup L) :=
    (h _ hY).trans (Subgroup.card_map_dvd _ π)
  rw [← hKtψ]
  exact LayerPDiv.dvd_card_map_of_perfect ψ hψker
    (LayerFacts.ggCommutator_eq_of_isQuasisimple hKtq) hp hpKt

end Model

end LayerPDivExc

section SixEDefs

@[expose] def GGE6PDivNonToralInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f), α ^ p = 1 →
      ¬ LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α) →
        ∀ X : Subgroup (adjointGroup .E6 (GaloisField 2 f)),
          IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → p ∣ Nat.card X

end SixEDefs

section SixE

theorem LayerPDivExc.dvd_card_of_isComponentOf_autFix_E6 (hW : GGWeylFamQuotSolvInput .E6)
    (h : GGE6PDivNonToralInput) {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) {α : MulAut (adjointGroup .E6 (GaloisField 2 f))}
    (hαD : α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f)) (hαp : α ^ p = 1)
    {X : Subgroup (adjointGroup .E6 (GaloisField 2 f))}
    (hX : IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α))) : p ∣ Nat.card X := by
  by_cases ht : LayerSixE.GGInndiagToral .E6 (GaloisField 2 f) (Subgroup.zpowers α)
  · have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    refine LayerPDivExc.dvd_card_of_isComponentOf_autFix_toral
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 _) hW hp hp2
      (by rw [hF]; exact LayerPDiv.dvd_sq_sub_one hpq) (fun β hβ => ?_) ht hX
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαp, one_zpow]
  · exact h f hf p hp hp2 hpq α hαD hαp ht X hX

theorem ggLayerPDivTag_E6_of_nonToral (hW : GGWeylFamQuotSolvInput .E6)
    (h : GGE6PDivNonToralInput) : GGLayerPDivTag .E6 := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy hN hdiag K hK
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have : Finite ↥(e6Data_valid.minGroup (GaloisField 2 f)) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  have hπ := e6Isogeny_surjective (GaloisField 2 f)
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hN hdiag
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hN p
    rw [hy] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  exact LayerPDivExc.dvd_card_of_isComponentOf_model hπ
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f))
    hkπ hp hN hα (fun X hX => LayerPDivExc.dvd_card_of_isComponentOf_autFix_E6 hW h hadm.2.1 hp
      hp2 hpq hαD hαp hX) hK

end SixE

section TwE6

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def GGTwE6PDivInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ α ∈ LayerSixE.twInndiagAut f, α ^ p = 1 →
      ∀ X : Subgroup (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers α)) → p ∣ Nat.card X

theorem ggLayerPDivTag_twistedE6_of_input (h : GGTwE6PDivInput) : GGLayerPDivTag .twistedE6 := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy hN hdiag K hK
  obtain ⟨⟨⟨-, hf, -⟩, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have : Finite (twistedE6Group 2 f) := by
    have : Finite (Module.End (GaloisField 2 (2 * f)) (Fin e6Data.d →₀ GaloisField 2 (2 * f))) :=
      Module.finite_of_finite (GaloisField 2 (2 * f))
    infer_instance
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hπker ▸ hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hN hdiag
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hN p
    rw [hy] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  exact LayerPDivExc.dvd_card_of_isComponentOf_model hπ hπker.le hkπ hp hN hα
    (fun X hX => h f hf p hp hp2 hpq α hαD hαp X hX) hK

end TwE6

end CFSG.StandardType
