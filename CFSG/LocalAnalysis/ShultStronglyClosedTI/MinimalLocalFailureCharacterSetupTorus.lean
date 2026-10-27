module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupTwoCoreFree

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup

open CFSG.BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G]

theorem map_centralizer_comap_of_injective {A : Type*} [Group A] (θ : A →* G)
    (hθ : Function.Injective θ) {W₀ : Subgroup G} (hW₀ : W₀ ≤ θ.range) :
    (Subgroup.centralizer ((W₀.comap θ : Subgroup A) : Set A)).map θ =
      θ.range ⊓ Subgroup.centralizer (W₀ : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    obtain ⟨b, rfl⟩ := hW₀ hh
    have hb : b ∈ W₀.comap θ := hh
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp ha b hb]
  · rintro ⟨⟨a, rfl⟩, hx⟩
    refine ⟨a, Subgroup.mem_centralizer_iff.mpr fun b hb => hθ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hx (θ b) hb

theorem map_normalizer_comap_of_le_range {A : Type*} [Group A] (θ : A →* G)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ θ.range) :
    (Subgroup.normalizer ((W₀.comap θ : Subgroup A) : Set A)).map θ =
      θ.range ⊓ Subgroup.normalizer (W₀ : Set G) := by
  rw [← Subgroup.comap_normalizer_eq_of_le_range hW₀, Subgroup.map_comap_eq]

theorem embedded_two_core_free_torus [Finite G] {k : Type*} [Field k] [Finite k] (f : ℕ)
    (hf : 2 ≤ f) (hcard : Nat.card k = 2 ^ f) (J : Subgroup G) (φ : J →* PSL2MatrixGroup k)
    (hφ : Function.Injective φ) (heven : Even (Nat.card J)) (hcore : CFSG.pCore 2 J = ⊥) :
    (∀ u ∈ J, ∀ v ∈ J, orderOf u = 2 → orderOf v = 2 → ∃ g ∈ J, g * u * g⁻¹ = v) ∧
    (∀ u ∈ J, orderOf u = 2 → ∃ W : Subgroup G, W ≤ J ∧ W ≠ ⊥ ∧ IsCyclic W ∧
      Odd (Nat.card W) ∧ (∀ w ∈ W, u * w * u⁻¹ = w⁻¹) ∧ u ∉ W ∧
      (∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ →
        J ⊓ Subgroup.centralizer (W₀ : Set G) = W ∧
        J ⊓ Subgroup.normalizer (W₀ : Set G) = W ⊔ Subgroup.zpowers u) ∧
      (∀ S : Sylow 2 J, Nat.card S = 2 → W ⊔ Subgroup.zpowers u = J)) ∧
    (∀ S : Sylow 2 J, 4 ≤ Nat.card S → ∀ N : Subgroup G, N ≤ J →
      (∀ g ∈ J, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → Odd (Nat.card N) → N = ⊥) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := φ.range
  let e : J ≃* A := MonoidHom.ofInjective hφ
  let θ : A →* G := J.subtype.comp e.symm.toMonoidHom
  have hθ : Function.Injective θ := J.subtype_injective.comp e.symm.injective
  have hrange : θ.range = J := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.symm a).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [θ]⟩
  have hmemJ : ∀ x ∈ J, ∃ a : A, θ a = x := fun x hx => by
    rw [← hrange] at hx
    exact hx
  have hcardA : Nat.card A = Nat.card J := Nat.card_congr e.toEquiv.symm
  have hAeven : Even (Nat.card A) := hcardA ▸ heven
  have hAcore : CFSG.pCore 2 A = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 e, hcore, Subgroup.map_bot]
  have hsylow : ∀ S : Sylow 2 J, ∃ S' : Sylow 2 A, Nat.card S' = Nat.card S := fun S =>
    ⟨default, by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, hcardA]⟩
  obtain ⟨hconj, htorus, hfour⟩ :=
    LinearModel.linear_two_core_free_subgroup_torus_and_involutions f hf hcard A hAeven hAcore
  refine ⟨fun u hu v hv hu2 hv2 => ?_, fun u hu hu2 => ?_, fun S hS N hNJ hNinv hNodd => ?_⟩
  ·
    obtain ⟨a, rfl⟩ := hmemJ u hu
    obtain ⟨b, rfl⟩ := hmemJ v hv
    rw [orderOf_injective θ hθ] at hu2 hv2
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj a b hu2 hv2)
    refine ⟨θ c, hrange ▸ ⟨c, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hc]
  ·
    obtain ⟨a, rfl⟩ := hmemJ u hu
    rw [orderOf_injective θ hθ] at hu2
    obtain ⟨W', hW'ne, hW'cyc, hW'odd, hW'inv, hW'u, hW', hW'two⟩ := htorus a hu2
    have hWJ : W'.map θ ≤ J := hrange ▸ Subgroup.map_le_range θ W'
    refine ⟨W'.map θ, hWJ, ?_, ?_, ?_, ?_, ?_, fun W₀ hW₀ hW₀ne => ?_, fun S hS => ?_⟩
    · exact (Subgroup.map_eq_bot_iff_of_injective _ hθ).not.mpr hW'ne
    · exact isCyclic_of_surjective _ (θ.subgroupMap_surjective W')
    · rwa [Subgroup.card_map_of_injective hθ]
    · rintro _ ⟨w, hw, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, hW'inv w hw]
    · intro haW
      have ha : a ∈ W' ⊓ Subgroup.zpowers a :=
        ⟨(Subgroup.mem_map_iff_mem hθ).mp haW, Subgroup.mem_zpowers a⟩
      rw [hW'u, Subgroup.mem_bot] at ha
      rw [ha, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    ·
      have hW₀range : W₀ ≤ θ.range := hrange ▸ hW₀.trans hWJ
      have hW₀le : W₀.comap θ ≤ W' := by
        have h := Subgroup.comap_mono (f := θ) hW₀
        rwa [Subgroup.comap_map_eq_self_of_injective hθ] at h
      have hW₀ne' : W₀.comap θ ≠ ⊥ := by
        intro h
        apply hW₀ne
        rw [← Subgroup.map_comap_eq_self hW₀range, h, Subgroup.map_bot]
      obtain ⟨hC, hN⟩ := hW' _ hW₀le hW₀ne'
      constructor
      · rw [← hrange, ← map_centralizer_comap_of_injective θ hθ hW₀range, hC]
      · rw [← hrange, ← map_normalizer_comap_of_le_range θ hW₀range, hN, Subgroup.map_sup,
          MonoidHom.map_zpowers]
    ·
      obtain ⟨S', hS'⟩ := hsylow S
      rw [← hS'] at hS
      have h := congrArg (Subgroup.map θ) (hW'two S' hS).2.2.2
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, hrange] at h
  ·
    obtain ⟨S', hS'⟩ := hsylow S
    rw [← hS'] at hS
    have hcoreA := hfour S' hS
    have hNrange : N ≤ θ.range := hrange ▸ hNJ
    have hNmap : (N.comap θ).map θ = N := Subgroup.map_comap_eq_self hNrange
    have hN'normal : (N.comap θ).Normal := ⟨fun n hn g => by
      change θ (g * n * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNinv (θ g) (hrange ▸ ⟨g, rfl⟩) (θ n) hn⟩
    have hN'odd : Odd (Nat.card (N.comap θ)) := by
      rwa [← Subgroup.card_map_of_injective hθ, hNmap]
    have hle : N.comap θ ≤ CFSG.oddCore A := le_sSup ⟨hN'normal, hN'odd⟩
    rw [hcoreA, le_bot_iff] at hle
    rw [← hNmap, hle, Subgroup.map_bot]

end CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup
