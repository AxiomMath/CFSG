module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.Adapter
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableCompatibility
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

namespace CFSG.SolvableSignalizer

open CFSG.SolvableSignalizer.Internal
open CFSG.Open CFSG.SignalizerFunctor.Helpers

private theorem lift_map_conj_embed {A G : Type*} [Group A] [Group G] {α : A →* MulAut G}
    (H : Subgroup G) (g : G) :
    (lift α H).map (MulAut.conj (embed α g)).toMonoidHom =
      lift α (H.map (MulAut.conj g).toMonoidHom) := by
  unfold lift
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

variable {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
  {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

private theorem compatible_primeSupported_iff {q : ℕ} (hq : q.Prime) (K : Subgroup (Ambient α)) :
    (solvableSignalizerCompatible p 1 (actor α) (values α θ) K ∧
      CFSG.SignalizerFunctor.Helpers.primeSupported {q} (Nat.card K)) ↔
      signalizerPrimeCompatible p 1 q (actor α) (values α θ) K := by
  have hpg := prime_supported_singleton_iff_pgroup q hq K
  constructor
  · rintro ⟨hcompat, hsup⟩
    exact ⟨hcompat.1, hpg.mp hsup⟩
  · rintro ⟨hcompat, hpgroup⟩
    refine ⟨⟨hcompat, ?_⟩, hpg.mpr hpgroup⟩
    have : Fact q.Prime := ⟨hq⟩
    have := hpgroup.isNilpotent
    infer_instance

private theorem maxCompatible_singleton_iff_maximal (d : Datum p α θ)
    {q : ℕ} (hq : q.Prime) (H : Subgroup G) :
    MaxCompatible p α θ {q} H ↔
      Maximal (signalizerPrimeCompatible p 1 q (actor α) (values α θ)) (lift α H) := by
  rw [maxCompatible_iff d {q} H, maximal_iff]
  constructor
  · rintro ⟨hH, hmax⟩
    refine ⟨(compatible_primeSupported_iff hq _).mp hH, fun K hK hle => ?_⟩
    exact le_antisymm hle (hmax K ((compatible_primeSupported_iff hq K).mpr hK) hle)
  · rintro ⟨hH, hmax⟩
    refine ⟨(compatible_primeSupported_iff hq _).mpr hH, fun K hK hle => ?_⟩
    exact (hmax ((compatible_primeSupported_iff hq K).mp hK) hle).ge

theorem exists_conj_eq_of_maxCompatible (d : Datum p α θ)
    (hlarge : p ^ 3 ≤ Nat.card A) {q : ℕ} (hq : q ∈ spectrum θ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : MaxCompatible p α θ {q} Q₁)
    (hQ₂ : MaxCompatible p α θ {q} Q₂) :
    ∃ c ∈ commonSignalizerWhole θ,
      Q₁.map (MulAut.conj c⁻¹).toMonoidHom = Q₂ := by
  have hqprime : q.Prime := hq.1
  have hdistinct : p ≠ q := fun h => d.notMem_spectrum (h ▸ hq)
  have hlarge' : p ^ (1 + 2) ≤ Nat.card (actor α) := by
    rw [card_actor]
    exact hlarge
  obtain ⟨e, he⟩ := signalizer_prime_transitivity p 1 q d.prime hqprime hdistinct
    (actor α) (isElemAbelian_actor d) hlarge' (values α θ)
    (solvableSignalizerConditions_values d).coprime
    (solvableSignalizerConditions_values d).normalized
    (solvableSignalizerConditions_values d).balanced (lift α Q₁) (lift α Q₂)
    ((maxCompatible_singleton_iff_maximal d hqprime Q₁).mp hQ₁)
    ((maxCompatible_singleton_iff_maximal d hqprime Q₂).mp hQ₂)
  have he_mem : e.val ∈ lift α (commonSignalizerWhole θ) := by
    rw [← signalizerCommonFixed_values d]
    exact e.property
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp he_mem
  have hEq : Q₁.map (MulAut.conj c).toMonoidHom = Q₂ := by
    apply lift_injective α
    rw [← lift_map_conj_embed Q₁ c, hce]
    exact he
  exact ⟨c⁻¹, inv_mem hc, by simpa only [inv_inv] using hEq⟩

theorem isComplete_of_ncard_spectrum_le_one (d : Datum p α θ)
    (hlarge : p ^ 3 ≤ Nat.card A) (hsupport : (spectrum θ).ncard ≤ 1) :
    IsComplete p α θ := by
  have hsubsing : ∀ {r s : ℕ}, r ∈ spectrum θ → s ∈ spectrum θ → r = s :=
    (Set.ncard_le_one_iff (finite_spectrum θ)).mp hsupport
  rcases Set.eq_empty_or_nonempty (spectrum θ) with hempty | ⟨q, hq⟩
  ·
    have hval : ∀ a : A, a ≠ 1 → θ a = ⊥ := by
      intro a ha
      rw [Subgroup.eq_bot_iff_card, Nat.eq_one_iff_not_exists_prime_dvd]
      intro r hr hrdvd
      have hmem : r ∈ spectrum θ := ⟨hr, a, ha, hrdvd⟩
      simp [hempty] at hmem
    have hcomp : completion θ = ⊥ := iSup₂_eq_bot.mpr hval
    rw [IsComplete, hcomp]
    exact compatible_bot d
  ·
    have hAt : ∀ H : Subgroup G, CompatibleAt p α θ {q} H ↔ Compatible p α θ H := by
      refine fun H => ⟨fun h => h.1, fun h => ⟨h, fun r hr hrdvd => ?_⟩⟩
      exact hsubsing (primeSupported_spectrum_of_compatible d h r hr hrdvd) hq
    have hMax : ∀ H : Subgroup G,
        MaxCompatible p α θ {q} H ↔ MaxCompatibleWhole p α θ H := fun H =>
      ⟨fun h => ⟨(hAt H).mp h.1, fun K hK hHK => h.2 K ((hAt K).mpr hK) hHK⟩,
        fun h => ⟨(hAt H).mpr h.1, fun K hK hHK => h.2 K ((hAt K).mp hK) hHK⟩⟩
    obtain ⟨-, a₀, ha₀, -⟩ := id hq
    have hC : Compatible p α θ (commonSignalizerWhole θ) := by
      have htop : (⊤ : Subgroup A) ≠ ⊥ := fun hbot =>
        ha₀ (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top a₀))
      exact ((compatible_values_and_commonSignalizer d).2.1 ⊤ htop a₀
        (Subgroup.mem_top a₀) ha₀).2
    obtain ⟨Q, hCQ, hQmax⟩ := Finite.exists_le_maximal hC
    have hQwhole : MaxCompatibleWhole p α θ Q :=
      ⟨hQmax.1, fun K hK hKQ => hQmax.2 hK hKQ⟩
    refine (isComplete_iff_existsUnique_maxCompatibleWhole d).mpr ⟨Q, hQwhole, fun H hH => ?_⟩
    obtain ⟨c, hc, hconj⟩ :=
      exists_conj_eq_of_maxCompatible d hlarge hq ((hMax Q).mpr hQwhole) ((hMax H).mpr hH)
    have hQmap : Q.map (MulAut.conj c⁻¹).toMonoidHom = Q :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := Q) (g := c⁻¹)).mp
        (Subgroup.le_normalizer (Q.inv_mem (hCQ hc)))
    rw [hQmap] at hconj
    exact hconj.symm

end CFSG.SolvableSignalizer
