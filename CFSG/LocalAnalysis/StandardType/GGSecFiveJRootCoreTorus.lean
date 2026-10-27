module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem jcore_inner_torus {U : Type} [Group U] (Δ : UniversalRootDatum U) {G : Type} [Group G]
    {ψ : U →* G} (hinj : Function.Injective ψ) {Bs : Subgroup G} (hstd : GGKGPosStdPos Δ ψ Bs)
    {y : G} (hy : y ∈ Bs)
    (hinn : ∃ g ∈ ψ.range, y * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    ∃ u ∈ ggTorus Δ, ∀ z, y * ψ z * y⁻¹ = ψ (u * z * u⁻¹) := by
  obtain ⟨_, ⟨w, rfl⟩, hc⟩ := hinn
  have hconj : ∀ z, y * ψ z * y⁻¹ = ψ (w⁻¹ * z * w⁻¹⁻¹) := by
    intro z
    have h1 : ψ (w⁻¹ * z * w) * (y * ψ w) = y * ψ w * ψ (w⁻¹ * z * w) :=
      Subgroup.mem_centralizer_iff.mp hc _ ⟨_, rfl⟩
    calc y * ψ z * y⁻¹ = y * ψ w * ψ (w⁻¹ * z * w) * (y * ψ w)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = ψ (w⁻¹ * z * w⁻¹⁻¹) := by rw [← h1, mul_inv_cancel_right, inv_inv]
  refine ⟨w⁻¹, ?_, hconj⟩
  refine Subgroup.mem_iInf.mpr fun γ => Subgroup.mem_iInf.mpr fun hγ => ?_
  obtain ⟨h, hh, hhz⟩ := hstd y hy γ hγ
  have hhN : h ∈ Subgroup.normalizer (Δ.rootGroup γ : Set U) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ
  have hC : h⁻¹ * w⁻¹ ∈ Subgroup.centralizer (Δ.rootGroup γ : Set U) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have e : w⁻¹ * z * w⁻¹⁻¹ = h * z * h⁻¹ := hinj (by rw [← hconj z, hhz z hz])
    calc z * (h⁻¹ * w⁻¹) = h⁻¹ * (h * z * h⁻¹) * w⁻¹ := by group
      _ = h⁻¹ * w⁻¹ * z := by rw [← e]; group
  have e : w⁻¹ = h * (h⁻¹ * w⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hhN (Subgroup.centralizer_le_normalizer _ hC)

@[expose] def GGJRootCoreTorusAt
    (t : StatedLieTag) : Prop :=
  ∀ (n f : ℕ), StatedLieAdmissible t n 2 f → 3 ≤ bnRank t n →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ f - 1 →
    ∀ u ∈ ggTorus (ggU t n f).D, u ^ p = 1 →
    ∀ J : Subgroup (ggU t n f).K,
      IsComponentOf J (Subgroup.centralizer ({u} : Set (ggU t n f).K)) →
      ∃ γ ∈ (ggU t n f).D.roots, ggRootLevi (ggU t n f).D γ ≤ J

private theorem jcore_range_inf_centralizer {L : Type} [Group L] {G : Type} [Group G]
    {ψ : L →* G} (hinj : Function.Injective ψ) {x : G} {s : L}
    (hs : (x, s) ∈ LayerFacts.ggConjPairs ψ) :
    ψ.range ⊓ Subgroup.centralizer {x} = (Subgroup.centralizer {s}).map ψ := by
  have key : ∀ z, ψ z * x = x * ψ z ↔ z * s = s * z := fun z => by
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul, ← LayerFacts.mem_ggConjPairs.mp hs z, hinj.eq_iff,
      mul_inv_eq_iff_eq_mul, eq_comm]
  ext g
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨z, rfl⟩, hz⟩
    exact ⟨z, (key z).mp hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, rfl⟩, (key z).mpr hz⟩

theorem ggJRootCoreAt_of_torus
    {t : StatedLieTag}
    (hZ : ∀ n f, StatedLieAdmissible t n 2 f → 3 ≤ bnRank t n →
      Subgroup.center (ggU t n f).K = ⊥)
    (hVI : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs L : Subgroup G) (n f : ℕ)
      (ψ : (ggU t n f).K →* G), GGKGPosLocalHyp p Bs L t n f ψ →
        ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (h : GGJRootCoreTorusAt t) : GGJRootCoreAt t := by
  intro G _ _ p Bs L J n f ψ y hloc hstd hy hJ
  have hinn := hVI G p Bs L n f ψ hloc y hy
  obtain ⟨⟨hp, hp2, hadm, h3⟩, ⟨hker, hrange, -, hpf⟩, ⟨hel, -, -⟩, -, -⟩ := hloc
  have hZ' := hZ n f hadm h3
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (le_bot_iff.mp (hker.trans hZ'.le))
  obtain ⟨u, hu, hyu⟩ := jcore_inner_torus (ggU t n f).D hinj hstd hy hinn
  have hmem : (y, u) ∈ LayerFacts.ggConjPairs ψ :=
    LayerFacts.mem_ggConjPairs.mpr fun z => (hyu z).symm
  have hyp : y ^ p = 1 := hel.2 y hy
  have hc := pow_mem hmem p
  rw [Prod.pow_mk, hyp] at hc
  have hc' := LayerFacts.mem_center_of_mem_ggConjPairs_one hinj hc
  rw [hZ'] at hc'
  subst hrange
  rw [jcore_range_inf_centralizer hinj hmem] at hJ
  obtain ⟨hJ', hmap⟩ := isComponentOf_comap_of_injective ψ hinj hJ
  obtain ⟨γ, hγ, hle⟩ := h n f hadm h3 p hp hp2 hpf u hu (Subgroup.mem_bot.mp hc') _ hJ'
  exact ⟨γ, hγ, (Subgroup.map_mono hle).trans hmap.le⟩

end CFSG.StandardType

end
