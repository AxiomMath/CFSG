module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmLift
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmModel
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSp

public section

namespace CFSG.StandardType

namespace OmNonsplit

open CFSG.Assembly QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  LayerCores LayerFacts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem eq_of_isComponentOf_of_le {G : Type*} [Group G] [Finite G] {H K₀ K₁ K₂ : Subgroup G}
    (h₁ : IsComponentOf K₁ H) (h₂ : IsComponentOf K₂ H) (hK : CFSG.IsQuasisimple K₀)
    (hK₁ : K₀ ≤ K₁) (hK₂ : K₀ ≤ K₂) : K₁ = K₂ := by
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute h₁ h₂ with h | h
  · exact h
  · exfalso
    have h1 : K₀ ≤ ⊥ := by
      rw [← h, ← ggCommutator_eq_of_isQuasisimple hK]
      exact Subgroup.commutator_mono hK₁ hK₂
    obtain ⟨u, u', huu⟩ := exists_mul_ne_of_isQuasisimple hK
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 u.2))
    have hu' : u' = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 u'.2))
    exact huu (by rw [hu, hu'])

theorem exists_component_spin (hQ : (polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hZ : Subgroup.center (spinGroup Q) = ⊥) {G : Type} [Group G] [Finite G]
    {ψ : spinGroup Q →* G} (hψ : Function.Injective ψ) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ f) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x) {s t : spinGroup Q}
    (hs : (x, s) ∈ ggConjPairs ψ) (ht : (y, t) ∈ ggConjPairs ψ) {Kx : Subgroup G}
    (hKx : IsComponentOf Kx (ψ.range ⊓ Subgroup.centralizer {x})) (hpK : ¬ p ∣ Nat.card Kx) :
    ∃ K'' : Subgroup G, IsComponentOf K'' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ Kx ≤ K'' ∧
      (∃ k ∈ K'', ∀ l ∈ K'', x⁻¹ * l * x = k⁻¹ * l * k) ∧ OmModel K K'' := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Finite (spinGroup Q) := Finite.of_injective _ hinj
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hσO : ∀ u, spinAction Q u ∈ O := fun u =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q u v
  have hZ1 : ∀ g : spinGroup Q, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hψ hg
    rwa [hZ, Subgroup.mem_bot] at h
  have hsp : s ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem hs p
    rwa [Prod.pow_mk, hx] at h)
  have htp : t ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem ht p
    rwa [Prod.pow_mk, hy] at h)
  have hst : s * t = t * s := by
    have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs ht)
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem ht hs))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hxy, mul_inv_cancel] at h
    have h1 := hZ1 _ h
    calc s * t = s * t * (t * s)⁻¹ * (t * s) := by group
      _ = t * s := by rw [h1, one_mul]
  have hap : spinAction Q s ^ p = 1 := by rw [← map_pow, hsp, map_one]
  have hbp : spinAction Q t ^ p = 1 := by rw [← map_pow, htp, map_one]
  have hab : spinAction Q s * spinAction Q t = spinAction Q t * spinAction Q s := by
    rw [← map_mul, ← map_mul, hst]
  have hC : ∀ u : spinGroup Q,
      ((Subgroup.centralizer (Subgroup.zpowers (spinAction Q u) : Set (V ≃ₗ[K] V)) ⊓ O) ⊓
        ⁅O, O⁆).comap (spinAction Q) =
        Subgroup.centralizer (Subgroup.zpowers u : Set (spinGroup Q)) := by
    intro u
    rw [← MonoidHom.map_zpowers]
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨⟨hg, -⟩, -⟩ w hw
      exact hinj (by rw [map_mul, map_mul]; exact hg _ ⟨w, hw, rfl⟩)
    · intro hg
      refine ⟨⟨?_, hσO g⟩, by rw [← hrange]; exact ⟨g, rfl⟩⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, hg w hw]
  have : Fintype (Subgroup.zpowers (spinAction Q s)) := Fintype.ofFinite _
  have hA : (Fintype.card (Subgroup.zpowers (spinAction Q s)) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hap))
  obtain ⟨β, S, hS, hSfix⟩ := exists_subCoreFamily_orthCent_fix hQ (hσO s) hp hp2 hap hA
  have hSinf := hS.inf_of_commutator_le (N := ⁅O, O⁆)
    (Subgroup.commutator_mono inf_le_right inf_le_right)
  have hS' := hSinf.comap (spinAction Q) hinj (by rw [hrange]; exact inf_le_right)
  rw [hC s] at hS'
  have hker : ψ.ker ≤ Subgroup.center (spinGroup Q) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  rw [ClNonsplit.range_inf_centralizer_eq hψ hs] at hKx
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) hS' hKx
  have hSO : S c ≤ (spinAction Q).range := by
    rw [hrange]
    exact (hSinf.1 c).trans inf_le_right
  have hpc : ¬ p ∣ Nat.card (S c) := by
    intro h
    apply hpK
    rw [Subgroup.card_map_of_injective hψ, LayerPDiv.card_comap_of_le_range hinj hSO]
    exact h
  obtain ⟨T, hTq, hTs, hpT, hScT⟩ := hSfix c hpc
  obtain ⟨L, hTL, hLq, hLC, hLs, ⟨kO, hkO, hkOinn⟩, hLM⟩ := exists_component_of_fix hQ
    (hσO s) (hσO t) hab hp hp2 hK hq1 hq2 hap hbp hA hTq hTs hpT
  have hLO : L ≤ ⁅O, O⁆ := by
    rw [← ggCommutator_eq_of_isQuasisimple hLq]
    exact Subgroup.commutator_mono (hLC.trans inf_le_right) (hLC.trans inf_le_right)
  have hLr : L ≤ (spinAction Q).range := hrange ▸ hLO
  let e : ↥((L.comap (spinAction Q)).map ψ) ≃* ↥L :=
    ((L.comap (spinAction Q)).equivMapOfInjective ψ hψ).symm.trans
      (((L.comap (spinAction Q)).equivMapOfInjective _ hinj).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLr)))
  refine ⟨(L.comap (spinAction Q)).map ψ, ?_, ?_, ?_, OmModel.of_mulEquiv e hLM⟩
  · rw [ClNonsplit.range_inf_centralizer_eq hψ ht, ← hC t]
    refine ⟨Subgroup.map_mono (Subgroup.comap_mono (le_inf hLC hLO)), ?_, ?_⟩
    · exact ggSubnormal_map ψ (ggSubnormal_comap _
        (ggSubnormal_mono hLs (le_inf hLC hLO) inf_le_left))
    · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLq)
  · exact Subgroup.map_mono (Subgroup.comap_mono ((le_of_eq hScT).trans hTL))
  · obtain ⟨k₀, hk₀⟩ := hLr hkO
    refine ⟨ψ k₀, ⟨k₀, show spinAction Q k₀ ∈ L from hk₀ ▸ hkO, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 : spinAction Q (s⁻¹ * u * s) = spinAction Q (k₀⁻¹ * u * k₀) := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hk₀]
      exact hkOinn _ hu
    have h2 : s⁻¹ * u * s = k₀⁻¹ * u * k₀ := hinj h1
    have h3 : x⁻¹ * ψ u * x = ψ (s⁻¹ * u * s) := by
      have h4 := hs (s⁻¹ * u * s)
      rw [show s * (s⁻¹ * u * s) * s⁻¹ = u by group] at h4
      rw [h4]
      group
    rw [h3, h2, map_mul, map_mul, map_inv]

end OmNonsplit

end CFSG.StandardType
