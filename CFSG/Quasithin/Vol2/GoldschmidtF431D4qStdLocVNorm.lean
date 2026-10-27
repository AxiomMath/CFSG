module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqSpec
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Torus

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.NFq
open scoped commutatorElement

theorem conj_mem_of_gen {G : Type} [Group G] {S : Set G} {H : Subgroup G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ H) {v : G} (hv : v ∈ Subgroup.closure S) : g * v * g⁻¹ ∈ H := by
  refine Subgroup.closure_induction (p := fun v _ => g * v * g⁻¹ ∈ H) h ?_ ?_ ?_ hv
  · simp
  · intro x y _ _ hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  · intro x _ hx
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx


set_option linter.unusedSectionVars false

section Basic

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem d4Zz_le_d4Va : d4Zz K σ ≤ d4Va σ :=
  (Subgroup.closure_le _).2 fun _ ⟨c, hc⟩ => hc ▸ d4x₆_mem_d4Va σ c

theorem d4Va_le_centralizer_d4x₁ (a : K) : d4Va σ ≤ Subgroup.centralizer {d4x₁ K σ a} :=
  (Subgroup.closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (commute_d4x₁_d4x₅ σ a c).eq.symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (commute_d4x₁_d4x₆ σ a c).eq.symm)

theorem mem_normalizer_d4Va {g : ModGL TwistTag.D4.tag K}
    (h1 : ∀ v ∈ d4Va σ, g * v * g⁻¹ ∈ d4Va σ) (h2 : ∀ v ∈ d4Va σ, g⁻¹ * v * g ∈ d4Va σ) :
    g ∈ Subgroup.normalizer (d4Va σ : Set (ModGL TwistTag.D4.tag K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h1 v, fun hv => ?_⟩
  have h3 := h2 _ hv
  have : g⁻¹ * (g * v * g⁻¹) * g = v := by group
  rwa [this] at h3

end Basic

section Rank1

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4x₂_mem_normalizer_d4Va {β : K} (hβ : σ β = β) :
    d4x₂ K β ∈ Subgroup.normalizer (d4Va σ : Set (ModGL TwistTag.D4.tag K)) := by
  have h1 : ∀ v ∈ d4Va σ, d4x₂ K β * v * (d4x₂ K β)⁻¹ ∈ d4Va σ := by
    intro v hv
    obtain ⟨e, f, he, hf, rfl⟩ := (mem_d4Va_iff_coord σ hσ).1 hv
    rw [d4x₂_conj_d4v σ hσ]
    refine (mem_d4Va_iff_coord σ hσ).2 ⟨e, e * β + f, he, ?_, rfl⟩
    rw [map_add, map_mul, he, hβ, hf]
  refine mem_normalizer_d4Va σ h1 fun v hv => ?_
  have h3 := h1 v hv
  rw [d4x₂_inv K β] at h3 ⊢
  exact h3

include hσ in
theorem trialityMiddleRep_mem_normalizer_d4Va :
    trialityMiddleRep K ∈ Subgroup.normalizer (d4Va σ : Set (ModGL TwistTag.D4.tag K)) := by
  have h1 : ∀ v ∈ d4Va σ, trialityMiddleRep K * v * (trialityMiddleRep K)⁻¹ ∈ d4Va σ :=
    fun v hv => conj_mem_of_gen (fun s hs => by
      rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [trialityMiddleRep_conj_d4x₅]
        exact d4x₆_mem_d4Va σ c
      · rw [trialityMiddleRep_conj_d4x₆]
        exact d4x₅_mem_d4Va σ c) hv
  have h2 : ∀ v ∈ d4Va σ, (trialityMiddleRep K)⁻¹ * v * trialityMiddleRep K ∈ d4Va σ :=
    fun v hv => conj_mem_of_gen (g := (trialityMiddleRep K)⁻¹) (fun s hs => by
      rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · have : (trialityMiddleRep K)⁻¹ * d4x₅ K c * ((trialityMiddleRep K)⁻¹)⁻¹ = d4x₆ K c := by
          rw [← trialityMiddleRep_conj_d4x₆ (c : K)]
          group
        rw [this]
        exact d4x₆_mem_d4Va σ c
      · have : (trialityMiddleRep K)⁻¹ * d4x₆ K c * ((trialityMiddleRep K)⁻¹)⁻¹ = d4x₅ K c := by
          rw [← trialityMiddleRep_conj_d4x₅ (c : K)]
          group
        rw [this]
        exact d4x₅_mem_d4Va σ c) hv
  exact mem_normalizer_d4Va σ h1 (by simpa using h2)

include hσ in
theorem d4Ma_le_normalizer_d4Va :
    d4Ma K σ ≤ Subgroup.normalizer (d4Va σ : Set (ModGL TwistTag.D4.tag K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> dsimp only
  · have hc := (mem_orbitField_D4_one σ).1 c.2
    rw [coe_orbitX_one_d4]
    exact d4x₂_mem_normalizer_d4Va σ hσ hc
  · have hc := (mem_orbitField_D4_one σ).1 c.2
    rw [coe_orbitY_one_d4, ← trialityMiddleRep_conj_d4x₂]
    exact mul_mem (mul_mem (trialityMiddleRep_mem_normalizer_d4Va σ hσ)
      (d4x₂_mem_normalizer_d4Va σ hσ hc)) (inv_mem (trialityMiddleRep_mem_normalizer_d4Va σ hσ))

end Rank1

section Unipotent

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4Vr_conj_mem_d4Va {q w : ModGL TwistTag.D4.tag K} (hq : q ∈ d4Vr K σ)
    (hw : w ∈ d4Va σ) : q * w * q⁻¹ ∈ d4Va σ := by
  have h1 : q * w * q⁻¹ = ⁅q, w⁆ * w := by
    rw [commutatorElement_def]
    group
  rw [h1]
  exact mul_mem (d4Zz_le_d4Va σ (commutator_mem_Zg σ hσ hq (d4Va_le_d4Vr σ hσ hw))) hw

include hσ in
theorem posUnipotent_conj_mem_d4Va {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :
    ∀ w ∈ d4Va σ, u * w * u⁻¹ ∈ d4Va σ := by
  obtain ⟨a, b, c, d, e, f, hb, he, hf, rfl⟩ :=
    exists_d4coord σ (toRingHom_pow_three_d4 σ hσ) hu
  intro w hw
  have hq : d4v K σ b c d e f ∈ d4Vr K σ :=
    d4v_mem_d4Vr σ (toRingHom_pow_three_d4 σ hσ) hb he hf
  have hw' := d4Vr_conj_mem_d4Va σ hσ hq hw
  have hcomm := Subgroup.mem_centralizer_singleton_iff.1
    (d4Va_le_centralizer_d4x₁ σ a hw')
  have : d4x₁ K σ a * d4v K σ b c d e f * w * (d4x₁ K σ a * d4v K σ b c d e f)⁻¹ =
      d4x₁ K σ a * (d4v K σ b c d e f * w * (d4v K σ b c d e f)⁻¹) * (d4x₁ K σ a)⁻¹ := by
    group
  rw [this, ← hcomm]
  simpa using hw'

include hσ in
theorem posUnipotent_le_normalizer_d4Va :
    graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      Subgroup.normalizer (d4Va σ : Set (ModGL TwistTag.D4.tag K)) := fun u hu =>
  mem_normalizer_d4Va σ (posUnipotent_conj_mem_d4Va σ hσ hu)
    (by simpa using posUnipotent_conj_mem_d4Va σ hσ (inv_mem hu))

end Unipotent

end CFSG.Quasithin.H13.F431.D4q.StdLoc
