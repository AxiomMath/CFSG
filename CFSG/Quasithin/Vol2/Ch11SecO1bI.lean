module

public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecO1A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat
open scoped IsMulCommutative

variable {G : Type} [Group G] {L V : Subgroup G} [IsMulCommutative ↥V] {D : FFModel}
  {K M : Type} [Field K] [AddCommGroup M] [Module K M] {LM : LinModel D K M}
  {π : D.Gam →* ↥(autOn L V)} {f : ↥V → M}

theorem exists_semilinear_conjV (hf : IsCoord LM (autOn L V) ⊥ π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {x₀ : M} (hx₀ : x₀ ≠ 0) {a : G} (haL : a ∈ Subgroup.normalizer (L : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    ∃ (T : M →+ M) (σ : K →+* K), (∀ (c : K) (x : M), T (c • x) = σ c • T x) ∧
      ∀ w, T (f w) = f (SecA.conjV V a haV w) := by
  set τ := SecA.conjV V a haV with hτ
  have hτZ : ∀ z ∈ (⊥ : Subgroup ↥V), τ z ∈ (⊥ : Subgroup ↥V) := fun z hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hτZ' : ∀ z ∈ (⊥ : Subgroup ↥V), τ⁻¹ z ∈ (⊥ : Subgroup ↥V) := fun z hz => by
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hinv : τ⁻¹ = SecA.conjV V a⁻¹ (Subgroup.inv_mem _ haV) := (SecA.conjV_inv V haV).symm
  have hτH' : ∀ h ∈ autOn L V, τ⁻¹ * h * τ ∈ autOn L V := fun h hh => by
    have := G2Q8.conjV_mul_conjV_inv_mem (Subgroup.inv_mem _ haL) (Subgroup.inv_mem _ haV) hh
    rwa [← hinv, inv_inv] at this
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear hcomm hx₀ τ hτZ hτZ' hτH'
  exact ⟨hf.autMap τ hτZ, σ, hσ, hf.autMap_apply τ hτZ⟩

theorem exists_point_conj (hf : IsCoord LM (autOn L V) ⊥ π f)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {V₁ : Subgroup G} {u₀ : M}
    (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀) {y : G} (hy : y ∈ L) :
    ∃ p : M, ∀ v : ↥V, (v : G) ∈ conjSubgroup V₁ y ↔ ∃ c : K, f v = c • p := by
  obtain ⟨γ, hγ⟩ := SecO1.IsCoord.exists_conj hf hLV hy
  obtain ⟨δ, hδ⟩ := SecO1.IsCoord.exists_conj hf hLV (L.inv_mem hy)
  have hyV := hLV hy
  have hyV' := hLV (L.inv_mem hy)
  have hγδ : ∀ x, LM.lin γ (LM.lin δ x) = x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [← hδ w (SecA.conjV V y⁻¹ hyV' w) (by rw [SecA.conjV_apply_coe]),
      ← hγ (SecA.conjV V y⁻¹ hyV' w) w (by rw [SecA.conjV_apply_coe]; group)]
  refine ⟨LM.lin δ u₀, fun v => ?_⟩
  rw [mem_conjSubgroup_iff]
  have hw : y * (v : G) * y⁻¹ = ((SecA.conjV V y hyV v : ↥V) : G) := by
    rw [SecA.conjV_apply_coe]
  rw [hw, hV₁, hγ v (SecA.conjV V y hyV v) (by rw [SecA.conjV_apply_coe])]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h1 : f v = LM.lin δ (f (SecA.conjV V y hyV v)) :=
      hδ _ v (by rw [SecA.conjV_apply_coe]; group)
    rw [h1, hγ v (SecA.conjV V y hyV v) (by rw [SecA.conjV_apply_coe]), hc, map_smul]
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, map_smul, hγδ]⟩

end CFSG.Quasithin.Vol2.Ch11.SecO1b
