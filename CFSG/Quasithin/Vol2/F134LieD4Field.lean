module

public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms

public section

namespace CFSG.Quasithin.F134.LieD4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem units_map_entrywiseHom_eq_pow {τ : Tag} {K : Type} [Field K] {δ : K →+* K} {m : ℕ}
    (hδ : ∀ c, δ c = c ^ m) {g : ModGL τ K} (hg : g ∈ diagonalGroup) :
    Units.map (entrywiseHom δ) g = g ^ m := by
  refine Units.ext (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.end_ext_single
    fun b => ?_)
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hg b
  have hpow : ∀ k : ℕ, ((g ^ k : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single b 1) = ((c : K) ^ k) • Finsupp.single b 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  rw [hpow, Units.coe_map]
  change entrywise δ (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) = _
  rw [entrywise_single, hc, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapRange_single,
    hδ, Finsupp.smul_single, smul_eq_mul, mul_one]

section Borel

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem commutator_mem_graphFixedPosUnipotent
    (hσ : Function.Surjective σ)
    {x y : ModGL t.tag K}
    (hx : x ∈ graphFixedRootBorel t K σ) (hy : y ∈ graphFixedRootBorel t K σ) :
    x * y * x⁻¹ * y⁻¹ ∈ graphFixedPosUnipotent t K σ := by
  have hx' : x ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hx
  have hy' : y ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hy
  rw [graphFixedRootBorel_eq_mul' hσ] at hx' hy'
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := hx'
  obtain ⟨u₂, hu₂, h₂, hh₂, rfl⟩ := hy'
  have hN₁ := graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh₁
  have hN₂ := graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh₂
  have hc : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = 1 := by
    rw [graphFixedRootTorus_mul_comm hh₁ hh₂]
    group
  have e : u₁ * h₁ * (u₂ * h₂) * (u₁ * h₁)⁻¹ * (u₂ * h₂)⁻¹ =
      u₁ * (h₁ * u₂ * h₁⁻¹) * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (h₂ * u₁⁻¹ * h₂⁻¹) * u₂⁻¹ := by group
  rw [e, hc, mul_one]
  exact mul_mem (mul_mem (mul_mem hu₁ ((Subgroup.mem_normalizer_iff.1 hN₁ u₂).1 hu₂))
    ((Subgroup.mem_normalizer_iff.1 hN₂ _).1 (inv_mem hu₁))) (inv_mem hu₂)

end Borel

section Triality


variable {K : Type} [Field K] [Finite K]

theorem exists_inv_mul_pow_mem_graphFixedPosUnipotent (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map α.toMonoidHom =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ k : ℕ, ∀ b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (b : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom →
        ((α b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K)⁻¹ *
          (b : ModGL TwistTag.D4.tag K) ^ (2 ^ k) ∈
            graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  obtain ⟨-, hNF, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσc
  obtain ⟨⟨g, δ⟩, hαe, -⟩ := hNF α
  simp only at hαe
  have hF : fieldActor σ δ ∈ graphFixedUnipotentStabilizer TwistTag.D4 K σ.toRingHom := by
    have := normalActor_mem (t := TwistTag.D4) σ 1 δ
    rwa [normalActor_one_left] at this
  have hgN : g ∈ Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hconj : MulAut.conj g = α * (fieldActor σ δ)⁻¹ := by rw [hαe, mul_inv_cancel_right]
    change Subgroup.map (MulAut.conj g).toMonoidHom _ = _
    rw [hconj, map_mulAut_mul, (inv_mem hF).1, hα]
  have hgB : (g : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨g.2, mem_normalizer_of_mem_normalizer_subgroupOf hUC hgN⟩
  obtain ⟨k, -, hδk, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq (by omega) hK3 δ
  refine ⟨k, fun b hb => ?_⟩
  have hb' : (b : ModGL TwistTag.D4.tag K) ∈
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := hb
  rw [graphFixedRootBorel_eq_mul' hσ] at hb'
  obtain ⟨u, hu, h, hh, hbe⟩ := hb'
  simp only at hbe
  have hhN := graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh
  have hδh : Units.map (entrywiseHom δ.toRingHom) h = h ^ (2 ^ k) :=
    units_map_entrywiseHom_eq_pow (δ := δ.toRingHom) hδk
      (torusGroup_le_diagonalGroup (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1)
  have hδu : Units.map (entrywiseHom δ.toRingHom) u ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    have h1 : fieldActor σ δ ⟨u, hUC hu⟩ ∈ ((graphFixedPosUnipotent TwistTag.D4 K
        σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
          (fieldActor σ δ).toMonoidHom := ⟨⟨u, hUC hu⟩, hu, rfl⟩
    rw [hF.1] at h1
    exact h1
  have hδb : ((fieldActor σ δ b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = Units.map (entrywiseHom δ.toRingHom) u * h ^ (2 ^ k) := by
    rw [coe_fieldActor, ← hbe, map_mul, hδh]
  obtain ⟨u', hu', hpow⟩ := exists_mul_pow_eq_mul_pow hu hhN (2 ^ k)
  have hβB : ((fieldActor σ δ b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    rw [hδb]
    exact mul_mem (graphFixedPosUnipotent_le_graphFixedRootBorel hδu)
      (pow_mem (graphFixedRootTorus_le_graphFixedRootBorel hh) _)
  have hαb : ((α b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      (g : ModGL TwistTag.D4.tag K) * ((fieldActor σ δ b : graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom) : ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K)⁻¹ := by
    rw [hαe]
    rfl
  have hcomm := commutator_mem_graphFixedPosUnipotent hσ hgB (inv_mem hβB)
  rw [inv_inv] at hcomm
  have key : ∀ x β v w y : ModGL TwistTag.D4.tag K, β = v * y →
      (x * β * x⁻¹)⁻¹ * (w * y) = (x * β⁻¹ * x⁻¹ * β) * (y⁻¹ * (v⁻¹ * w) * y⁻¹⁻¹) := by
    intro x β v w y hβ
    subst hβ
    group
  have e := key g _ _ u' (h ^ (2 ^ k)) hδb
  rw [← hαb, ← hpow, hbe] at e
  rw [e]
  refine mul_mem hcomm ?_
  exact (Subgroup.mem_normalizer_iff.1 (inv_mem (pow_mem hhN _)) _).1
    (mul_mem (inv_mem hδu) hu')

end Triality

end CFSG.Quasithin.F134.LieD4
