module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

private theorem transport_abstract {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    (hker : ψ.ker = Subgroup.center K) (hcent : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ c : ↥(Subgroup.normalizer (ψ.range : Set G)) →* MulAut (K ⧸ Subgroup.center K),
      Function.Injective c ∧
      (∀ k : K, c ⟨ψ k, Subgroup.le_normalizer ⟨k, rfl⟩⟩ =
        MulAut.conj (k : K ⧸ Subgroup.center K)) ∧
      ∀ (b : ↥(Subgroup.normalizer (ψ.range : Set G))) (k₀ z z' : K),
        ((b : G) * ψ k₀)⁻¹ * ψ z * ((b : G) * ψ k₀) = ψ z' ↔
          (c b * MulAut.conj (k₀ : K ⧸ Subgroup.center K))⁻¹ *
              MulAut.conj (z : K ⧸ Subgroup.center K) *
              (c b * MulAut.conj (k₀ : K ⧸ Subgroup.center K)) =
            MulAut.conj (z' : K ⧸ Subgroup.center K) := by
  classical
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  let e : (K ⧸ Subgroup.center K) ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have he : ∀ k : K, ((e (k : K ⧸ Subgroup.center K) : ψ.range) : G) = ψ k := fun k => rfl
  let c : ↥(Subgroup.normalizer (ψ.range : Set G)) →* MulAut (K ⧸ Subgroup.center K) :=
    (MulAut.congr e.symm).toMonoidHom.comp (Subgroup.normalizerMonoidHom ψ.range)
  have hc : ∀ (b : ↥(Subgroup.normalizer (ψ.range : Set G))) (q : K ⧸ Subgroup.center K),
      ((e (c b q) : ψ.range) : G) = (b : G) * (e q : G) * (b : G)⁻¹ := fun b q => by
    show ((e (e.symm ((Subgroup.normalizerMonoidHom ψ.range b) (e q))) : ψ.range) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hinj : Function.Injective c := by
    intro b b' hbb'
    have h1 : ∀ x : ψ.range, (b : G) * (x : G) * (b : G)⁻¹ = (b' : G) * (x : G) * (b' : G)⁻¹ := by
      intro x
      have h := congrArg
        (fun a : MulAut (K ⧸ Subgroup.center K) => ((e (a (e.symm x)) : ψ.range) : G)) hbb'
      simp only [hc, MulEquiv.apply_symm_apply] at h
      exact h
    have h2 : (b' : G)⁻¹ * (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := h1 ⟨x, hx⟩
      calc x * ((b' : G)⁻¹ * (b : G))
          = (b' : G)⁻¹ * ((b' : G) * x * (b' : G)⁻¹) * (b : G) := by group
        _ = (b' : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by rw [h]
        _ = (b' : G)⁻¹ * (b : G) * x := by group
    rw [hcent, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2.symm
  have hb0 : ∀ k : K, ψ k ∈ Subgroup.normalizer (ψ.range : Set G) :=
    fun k => Subgroup.le_normalizer ⟨k, rfl⟩
  have hcompat : ∀ k : K, c ⟨ψ k, Subgroup.le_normalizer ⟨k, rfl⟩⟩ =
      MulAut.conj (k : K ⧸ Subgroup.center K) := by
    intro k
    ext q
    refine QuotientGroup.induction_on q fun k' => ?_
    apply e.injective
    apply Subtype.ext
    rw [hc]
    show ψ k * ψ k' * (ψ k)⁻¹ =
      ((e (((k * k' * k⁻¹ : K)) : K ⧸ Subgroup.center K) : ψ.range) : G)
    rw [he]
    simp
  refine ⟨c, hinj, hcompat, fun b k₀ z z' => ?_⟩
  have hL : ((b * ⟨ψ k₀, hb0 k₀⟩)⁻¹ * ⟨ψ z, hb0 z⟩ * (b * ⟨ψ k₀, hb0 k₀⟩) :
        ↥(Subgroup.normalizer (ψ.range : Set G))) = ⟨ψ z', hb0 z'⟩ ↔
      ((b : G) * ψ k₀)⁻¹ * ψ z * ((b : G) * ψ k₀) = ψ z' := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hR : (c b * MulAut.conj (k₀ : K ⧸ Subgroup.center K))⁻¹ *
        MulAut.conj (z : K ⧸ Subgroup.center K) *
        (c b * MulAut.conj (k₀ : K ⧸ Subgroup.center K)) =
      c ((b * ⟨ψ k₀, hb0 k₀⟩)⁻¹ * ⟨ψ z, hb0 z⟩ * (b * ⟨ψ k₀, hb0 k₀⟩)) := by
    simp only [map_mul, map_inv, hcompat]
  rw [hR, ← hcompat z', hinj.eq_iff]
  exact hL.symm

theorem ggTransportHom {t : StatedLieTag} {n f : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : (ggU t n f).K →* G} (hset : GGKnownSetting t n f ψ) :
    ∃ c : ↥(Subgroup.normalizer (ψ.range : Set G)) →* GGAutU t n f, Function.Injective c ∧
      (∀ k : (ggU t n f).K, c ⟨ψ k, Subgroup.le_normalizer ⟨k, rfl⟩⟩ = ggPsiU t n f k) ∧
      ∀ b : ↥(Subgroup.normalizer (ψ.range : Set G)),
        GGPsiInnerDiag (ggU t n f).D ψ (b : G) ↔ GGInnDiagU t n f (c b) := by
  have hker : ψ.ker = Subgroup.center (ggU t n f).K := by
    refine le_antisymm hset.2.1 fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hmem : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
    rw [hset.2.2.2, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨c, hinj, hcompat, hiff⟩ := transport_abstract ψ hker hset.2.2.2
  refine ⟨c, hinj, hcompat, fun b => ?_⟩
  unfold GGInnDiagU GGPsiInnerDiag
  constructor
  · rintro ⟨g, ⟨k₀, rfl⟩, hg⟩
    refine ⟨ggPsiU t n f k₀, ⟨k₀, rfl⟩, fun γ hγ => ?_⟩
    obtain ⟨h, hh, hz⟩ := hg γ hγ
    exact ⟨h, hh, fun z hz' => (hiff b k₀ z (h * z * h⁻¹)).1 (hz z hz')⟩
  · rintro ⟨g', ⟨k₀, rfl⟩, hg'⟩
    refine ⟨ψ k₀, ⟨k₀, rfl⟩, fun γ hγ => ?_⟩
    obtain ⟨h, hh, hz⟩ := hg' γ hγ
    exact ⟨h, hh, fun z hz' => (hiff b k₀ z (h * z * h⁻¹)).2 (hz z hz')⟩

end Universal

end CFSG.StandardType
