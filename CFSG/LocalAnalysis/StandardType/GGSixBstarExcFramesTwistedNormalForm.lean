module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section NormalFormTw


theorem exists_normalForm_twistedE6 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {θ : K →+* K}
    (hθ : σ.toRingHom = θ) {p : ℕ} (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K θ))
    (hα : α ^ p = 1) :
    ∃ (Dg : Subgroup (ModGL TwistTag.E6.tag K)) (x : ModGL TwistTag.E6.tag K) (δ : K ≃+* K),
      Dg ≤ Subgroup.normalizer
        (graphFixedRootGroup TwistTag.E6 K θ : Set (ModGL TwistTag.E6.tag K)) ∧
      (∀ d ∈ Dg, d ^ 3 ∈ graphFixedRootGroup TwistTag.E6 K θ) ∧
      x ∈ graphFixedRootGroup TwistTag.E6 K θ ⊔ Dg ∧ δ ^ p = 1 ∧
      ∀ h : ↥(graphFixedRootGroup TwistTag.E6 K θ), (α h : ModGL TwistTag.E6.tag K) =
        x * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) * x⁻¹ := by
  subst hθ
  obtain ⟨-, -, -, -, -, hΔ, hfa, hex, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, δ, hgαu⟩ := hex α
  have hδp : δ ^ p = 1 := by
    have h1 : (Θ α) ^ p = 1 := by rw [← map_pow, hα, map_one]
    rwa [hΘ α g u δ hgαu] at h1
  set b := compatDiag TwistTag.E6 σ.toRingHom u with hb
  have hbc' : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (b i) :=
    fun i => compatDiag_perm u i
  have hbc : b ∈ TableB.TwE6.compat σ.toRingHom := fun i => compatDiag_perm u i
  have hdN : rootDiagUnit TwistTag.E6.tag b ∈
      Subgroup.normalizer (graphFixedRootGroup TwistTag.E6 K σ.toRingHom : Set (ModGL _ K)) :=
    rootDiagUnit_mem_normalizer_graphFixedRootGroup hbc'
  have hb3 : b ^ 3 ∈ TableB.TwE6.torus₀ σ.toRingHom :=
    TwE6Toral.pow_three_mem_torus₀ (TwE6Toral.two_le_two_pow hf) hK hσ hbc
  have hd3 : rootDiagUnit TwistTag.E6.tag (b ^ 3) ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    obtain ⟨s, hs, hst⟩ := hb3
    rw [← hst]
    exact TableB.TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  have hcube : ∀ d ∈ Subgroup.zpowers (rootDiagUnit TwistTag.E6.tag b),
      d ^ 3 ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    intro d hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    have h3 : (rootDiagUnit TwistTag.E6.tag b ^ j) ^ 3 =
        (rootDiagUnit TwistTag.E6.tag b ^ 3) ^ j := by
      rw [← zpow_natCast (rootDiagUnit TwistTag.E6.tag b ^ j) 3, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast]
    rw [h3, CFSG.LieType.Chevalley.rootDiagUnit_pow]
    exact Subgroup.zpow_mem _ hd3 j
  refine ⟨Subgroup.zpowers (rootDiagUnit TwistTag.E6.tag b),
    (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b, δ, Subgroup.zpowers_le.2 hdN,
    hcube, Subgroup.mul_mem_sup g.2 (Subgroup.mem_zpowers _), hδp, ?_⟩
  intro h
  have h1 : ((fieldActor σ δ h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) = Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) :=
    hfa δ h
  have h2 := hΔ u (fieldActor σ δ h)
  rw [hgαu]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h2, h1]
  simp only [mul_inv_rev, mul_assoc]
  rfl

end NormalFormTw

end ExcFrames

end CFSG.StandardType
