module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizerX

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint


section JTheta

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

omit
  [Algebra k K] in
theorem highRootSL2_eq_range_thetaSL2 (h2 : (2 : K) = 0) :
    EPilot.highRootSL2 .E6 K = (thetaSL2 K).range := by
  rw [range_thetaSL2 h2, Subgroup.closure_union]
  rfl

theorem mem_thetaRankOneGroup_of_mem_highRootSL2 [Finite k] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {g : ModGL TwistTag.E6.tag K} (hgJ : g ∈ EPilot.highRootSL2 .E6 K)
    (hgF : twistHom TwistTag.E6 K σ g = g) : g ∈ thetaRankOneGroup (algebraMap k K) := by
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  rw [highRootSL2_eq_range_thetaSL2 hK2] at hgJ
  obtain ⟨B, rfl⟩ := hgJ
  have hσB : Matrix.SpecialLinearGroup.map σ B = B :=
    thetaSL2_injective hK2 (by rw [← twistHom_thetaSL2 hK2, hgF])
  obtain ⟨B₀, rfl⟩ :=
    F4Pilot.exists_map_eq_of_map_eq (algebraMap k K) σ (sigma_eq_self_iff hk hσ) B hσB
  rw [thetaRankOneGroup_eq_range hK2]
  exact ⟨B₀, rfl⟩

omit [Algebra k K] in
theorem mem_highTorusLine_of_mem_highRootSL2 [Finite K] [CharP K 2] {m : ModGL .E6 K}
    (hm : m ∈ EPilot.highRootSL2 .E6 K) {c : Kˣ} (hc : 3 ≤ orderOf c)
    (hmc : m * rootDiagUnit .E6 (EPilot.highDiag .E6 c) =
      rootDiagUnit .E6 (EPilot.highDiag .E6 c) * m) :
    m ∈ EPilot.highTorusLine .E6 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hmT : m ∈ toralCentralizer .E6 K (EPilot.highDiag .E6 c) := by
    refine mem_toralCentralizer.2 ⟨EPilot.highRootSL2_le_adjointGroup hm, ?_⟩
    rw [← hmc, mul_inv_cancel_right]
  obtain ⟨hTD, hdisjT, hcommT⟩ := EPilot.toralCentralizer_highDiag_eq_sup (K := K) (τ := .E6)
    (Or.inl rfl) (ringChar.eq K 2) hc
  rw [hTD] at hmT
  obtain ⟨⟨t, d⟩, ⟨ht, hd, htd⟩, -⟩ := existsUnique_mul_of_commute (disjoint_iff.1 hdisjT)
    (fun a ha b hb => (hcommT a ha b hb).eq) _ hmT
  dsimp only at ht hd htd
  have hdJ : d ∈ (thetaSL2 K).range := by
    have e : d = t⁻¹ * m := by rw [htd, inv_mul_cancel_left]
    rw [e, ← highRootSL2_eq_range_thetaSL2 h2]
    exact mul_mem (inv_mem (EPilot.highTorusLine_le_highRootSL2 (Or.inl rfl) ht)) hm
  have hd1 : d = 1 := (Subgroup.disjoint_def.1 (disjoint_range_thetaSL2_subsystemGroup h2)) hdJ
    (rootSpan_perpRoots_le_subsystemGroup hd)
  rw [htd, hd1, mul_one]
  exact ht

end JTheta

section Centralizer

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem mem_highRootSL2_of_mem_centralizer_su6Levi (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {g : ModGL .E6 K} (hgA : g ∈ adjointGroup .E6 K)
    (hgD : ∀ x : ModGL .E6 K, x ∈ su6Levi σ → g * x = x * g) :
    g ∈ EPilot.highRootSL2 .E6 K := by
  obtain ⟨-, hgJ⟩ := core_X hf2 hk hK hσ hgA 1 (RingEquiv.refl K) (fun x hx => by
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) x = x :=
      Units.ext (entrywise_id _)
    rw [rootDiagUnit_one, e1, one_mul, inv_one, mul_one, hgD x hx, mul_inv_cancel_right])
  rwa [rootDiagUnit_one, mul_one] at hgJ

theorem centralizer_su6Levi_inf_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ = thetaRankOneGroup (algebraMap k K) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨hLX, -⟩ := su6Levi_facts hf hk hK hσ
  refine le_antisymm (fun g hg => ?_) (le_inf (fun j hj => mem_centralizer_iff.2 fun d hd =>
    (mem_centralizer_iff.1 (hLX hd) j hj).symm) (thetaRankOneGroup_le_C0 hf hk hK hσ))
  obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
  have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgC).1
  have hgF : twistHom TwistTag.E6 K σ g = g :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hgC)).2
  have hgJ := mem_highRootSL2_of_mem_centralizer_su6Levi (g := g) hf2 hk hK hσ hgA
    fun x hx => (mem_centralizer_iff.1 hgc x hx).symm
  exact mem_thetaRankOneGroup_of_mem_highRootSL2 hf hk hK hσ hgJ hgF

end Centralizer

end CFSG.SeitzReduction.TwistedE6Pilot
