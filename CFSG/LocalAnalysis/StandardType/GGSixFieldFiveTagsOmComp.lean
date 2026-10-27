module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOmCore

public section

namespace CFSG.StandardType

namespace FieldFiveOm

open CFSG.Assembly QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  LayerCores LayerFacts OmNonsplit

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_fixedCore_component_om (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 2)
    (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {G : Type} [Group G] [Finite G] {ψ : spinGroup Q →* G} (hψ : Function.Injective ψ)
    {z : G} {t : spinGroup Q} (ht : (z, t) ∈ ggConjPairs ψ) (ht5 : t ^ 5 = 1)
    {S : Subgroup (V ≃ₗ[K] V)} (hSq : CFSG.IsQuasisimple S)
    (hSO : S ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hSfix : ∀ M ∈ S, ∀ v, M (spinAction Q t v - v) = spinAction Q t v - v) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {z}) ∧
      (S.comap (spinAction Q)).map ψ ≤ K' ∧
      ∀ (w : G) (s : spinGroup Q), (w, s) ∈ ggConjPairs ψ → s ^ 5 = 1 → s * t = t * s →
        ¬ GGNbrClauseFiveMarking 5 w K' ∧
        ((∀ M ∈ S, M * spinAction Q s = spinAction Q s * M ∧
            ∀ v, M (spinAction Q s v - v) = spinAction Q s v - v) ∨
          (5 ∣ Nat.card K' ∧ w ∉ Subgroup.centralizer (K' : Set G))) := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Finite (spinGroup Q) := Finite.of_injective _ hinj
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hσO : ∀ u, spinAction Q u ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun u =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q u v
  have hT5 : spinAction Q t ^ 5 = 1 := by rw [← map_pow, ht5, map_one]
  obtain ⟨L, hSL, hLq, hLC, hLs, hLM, hLb⟩ :=
    exists_fixedCore_orth hQ hK (hσO t) hT5 hSq hSO hSfix
  have hLO : L ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [← ggCommutator_eq_of_isQuasisimple hLq]
    exact Subgroup.commutator_mono (hLC.trans inf_le_right) (hLC.trans inf_le_right)
  have hLr : L ≤ (spinAction Q).range := hrange ▸ hLO
  let e : ↥((L.comap (spinAction Q)).map ψ) ≃* ↥L :=
    ((L.comap (spinAction Q)).equivMapOfInjective ψ hψ).symm.trans
      (((L.comap (spinAction Q)).equivMapOfInjective _ hinj).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLr)))
  have hC := comap_spinAction_centralizer hinj hrange (Subgroup.zpowers t)
  rw [MonoidHom.map_zpowers] at hC
  refine ⟨(L.comap (spinAction Q)).map ψ, ?_, Subgroup.map_mono (Subgroup.comap_mono hSL),
    fun w s hws hs5 hst => ?_⟩
  · rw [ClNonsplit.range_inf_centralizer_eq hψ ht, ← hC]
    refine ⟨Subgroup.map_mono (Subgroup.comap_mono (le_inf hLC hLO)), ?_, ?_⟩
    · exact ggSubnormal_map ψ (ggSubnormal_comap _
        (ggSubnormal_mono hLs (le_inf hLC hLO) inf_le_left))
    · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLq)
  have hb5 : spinAction Q s ^ 5 = 1 := by rw [← map_pow, hs5, map_one]
  have hbT : spinAction Q s * spinAction Q t = spinAction Q t * spinAction Q s := by
    rw [← map_mul, ← map_mul, hst]
  obtain ⟨k, hkL, hkinn, hk5, hk1, hkc⟩ := hLb _ (hσO s) hbT hb5
  obtain ⟨k₀, hk₀⟩ := hLr hkL
  have hk₀K : ψ k₀ ∈ (L.comap (spinAction Q)).map ψ :=
    ⟨k₀, show spinAction Q k₀ ∈ L from hk₀ ▸ hkL, rfl⟩
  have hconj : ∀ u : spinGroup Q, w⁻¹ * ψ u * w = ψ (s⁻¹ * u * s) := by
    intro u
    have h4 := hws (s⁻¹ * u * s)
    rw [show s * (s⁻¹ * u * s) * s⁻¹ = u by group] at h4
    rw [h4]
    group
  have hinn : ∀ l ∈ (L.comap (spinAction Q)).map ψ, w⁻¹ * l * w = (ψ k₀)⁻¹ * l * ψ k₀ := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : spinAction Q (s⁻¹ * u * s) = spinAction Q (k₀⁻¹ * u * k₀) := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hk₀]
      exact hkinn _ hu
    rw [hconj, hinj h1, map_mul, map_mul, map_inv]
  refine ⟨not_ggNbrClauseFiveMarking_of_omModel (f := 1) (by rw [hK, pow_one])
    (OmModel.of_mulEquiv e hLM) hp (by norm_num) (by norm_num) (by norm_num)
    ⟨ψ k₀, hk₀K, hinn⟩, ?_⟩
  by_cases hk : k = 1
  · exact Or.inl (hk1 hk)
  right
  have hk₀1 : k₀ ≠ 1 := fun h => hk (by rw [← hk₀, h, map_one])
  refine ⟨?_, fun hwK => hk (hkc fun l hl => ?_)⟩
  · have hψk5 : (⟨ψ k₀, hk₀K⟩ : ↥((L.comap (spinAction Q)).map ψ)) ^ 5 = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      have h1 : k₀ ^ 5 = 1 := hinj (by rw [map_pow, hk₀, hk5, map_one])
      rw [← map_pow, h1, map_one]
    have hψk1 : (⟨ψ k₀, hk₀K⟩ : ↥((L.comap (spinAction Q)).map ψ)) ≠ 1 := by
      intro h
      exact hk₀1 (hψ (by simpa using congrArg Subtype.val h))
    rw [← orderOf_eq_prime hψk5 hψk1]
    exact orderOf_dvd_natCard _
  · obtain ⟨u, hu⟩ := hLr hl
    have hψu : ψ u ∈ (L.comap (spinAction Q)).map ψ :=
      ⟨u, show spinAction Q u ∈ L from hu ▸ hl, rfl⟩
    have h2 : w⁻¹ * ψ u * w = ψ u := by
      have h3 := Subgroup.mem_centralizer_iff.mp hwK (ψ u) hψu
      rw [mul_assoc, h3, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 : (ψ k₀)⁻¹ * ψ u * ψ k₀ = ψ u := by rw [← hinn (ψ u) hψu, h2]
    have h4 : ψ (u * k₀) = ψ (k₀ * u) := by
      rw [map_mul, map_mul]
      calc ψ u * ψ k₀ = ψ k₀ * ((ψ k₀)⁻¹ * ψ u * ψ k₀) := by group
        _ = ψ k₀ * ψ u := by rw [h3]
    rw [← hu, ← hk₀, ← map_mul, ← map_mul, hψ h4]

end FieldFiveOm

end CFSG.StandardType
