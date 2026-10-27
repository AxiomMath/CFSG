module

public import CFSG.LieType.Chevalley.GraphFixedParabolicPointwiseRigidity
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section D4Core


theorem burnsideF411a_sigma_pow_three {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) : σ ^ 3 = 1 :=
  RingEquiv.ext fun c => by
    rw [pow_succ, pow_two, RingAut.mul_apply, RingAut.mul_apply]
    exact ringEquiv_cube_apply_eq hK hσ c

theorem burnsideF411a_D4_inner_of_fix {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (x : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom →
        α x = x) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_fixed_Sylow_opposition TwistTag.D4 K p σ w₀ hw₀).2.2.2.2.2 α
  obtain ⟨u, δ, rfl⟩ := exists_normalActor_eq_D4 (Fact.out : p.Prime) hf hK σ hσ ⟨hU, hV⟩
  have hσ3 : σ ^ TwistTag.D4.order = 1 := burnsideF411a_sigma_pow_three hK hσ
  have hJ : (∅ : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ := by
    have : Nonempty (Fin TwistTag.D4.foldedTag.rank) := ⟨⟨0, by decide⟩⟩
    exact Set.empty_ne_univ
  have hform : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ((MulAut.conj c * normalActor σ u δ) x : ModGL TwistTag.D4.tag K) =
        (c : ModGL TwistTag.D4.tag K) *
          rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ.toRingHom u) *
          Units.map (entrywiseHom δ.toRingHom) x *
          (rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ.toRingHom u))⁻¹ *
          (c : ModGL TwistTag.D4.tag K)⁻¹ := by
    intro x
    rw [normalActor, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, coe_compatDiagAutHom, coe_fieldActor, Subgroup.coe_inv]
    group
  obtain ⟨-, z, -, hz, hαz⟩ :=
    (diagram_fixed_parabolic_radical_diagonal_field_pointwise_rigidity TwistTag.D4 K σ hσ3
      hJ).2.1 (c : ModGL TwistTag.D4.tag K) c.2 (compatDiag TwistTag.D4 σ.toRingHom u)
      (fun i => compatDiag_perm u i) δ (ringAut_mul_comm K δ σ) _ hform
      fun x hx => hα x (graphFixedParabolicRadical_le_graphFixedPosUnipotent ∅ hx)
  exact ⟨⟨z, hz⟩, hαz⟩

theorem burnsideF411a_D4_inner_of_fix_sylow {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (S : Sylow p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : ∀ s ∈ (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), α s = s) :
    ∃ g, α = MulAut.conj g := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K p σ w₀ hw₀).1
  obtain ⟨x, hx⟩ :=
    MulAction.exists_smul_eq (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) P₀ S
  have hβ : ∀ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (v : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom →
        ((MulAut.conj x)⁻¹ * α * MulAut.conj x) v = v := by
    intro v hv
    have hv' : v ∈ (P₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [hP₀]
      exact Subgroup.mem_subgroupOf.2 hv
    have hxv : x * v * x⁻¹ ∈ (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      have h1 := Subgroup.smul_mem_pointwise_smul v (MulAut.conj x) (P₀ : Subgroup _) hv'
      rwa [MulAut.smul_def, MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ hxv, MulAut.conj_inv_apply]
    group
  obtain ⟨g, hg⟩ := burnsideF411a_D4_inner_of_fix hf hK σ hσ _ hβ
  refine ⟨x * g * x⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg]
  group

end D4Core

end CFSG.ASVolI
